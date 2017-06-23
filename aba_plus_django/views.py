"""Copyright 2017 Ziyi Bao, Department of Computing, Imperial College London

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License."""

from django.views import generic
from django.http import HttpResponseRedirect
from django.core.urlresolvers import reverse
from django.forms import formset_factory
import json

from .forms.forms import BabaWorldForm, BabaWorldsForm
from abap_parser import *
from aspartix_interface import *
from baba import BABAProgramParser as Parser
from baba import Semantics, SemanticsUtils, babaUtilities

SOLVER_INPUT = "input_for_solver.lp"
TURNSTILE = "&#x22a2;"
R_ARROW = "&rarr;"
L_ARROW = "&larr;"
OVERLINE = "<span style=\"text-decoration: overline\">{}</span>"

BOTH_ATTACKS = 3

STABLE = 1
GROUNDED = 2
COMPLETE = 3
PREFERRED = 4
IDEAL = 5

extension_type_names = {STABLE: "stable", GROUNDED: "grounded",
                      COMPLETE: "complete", PREFERRED: "preferred", IDEAL: "ideal"}

attack_type_names = {NORMAL_ATK: "normal attack", REVERSE_ATK: "reverse attack", BOTH_ATTACKS: "both attacks"}

NOT_HIGHLIGHTED1 = 1
NOT_HIGHLIGHTED2 = 2
HIGHLIGHTED = 3

#maps session keys to calculation results
results = {}


class IndexView(generic.ListView):
    template_name = 'aba_plus_django/index.html'

    def get_queryset(self):
        return None

    def post(self, request, **kwargs):
        if "submit_text" in request.POST:
            request.session['input'] = request.POST['input_text']

        elif "submit_file" in request.POST:
            file = request.FILES['myfile']
            str = ""
            for chunk in file.chunks():
                str += chunk.decode("utf-8")
            request.session['input'] = str

        request.session['auto_WCP'] = False
        request.session['to_compute'] = True

        return HttpResponseRedirect(reverse('aba_plus_django:results'))


class ResultsView(generic.ListView):
    template_name = 'aba_plus_django/results.html'
    context_object_name = 'input'

    def get_queryset(self):
        return self.request.session['input'].replace("\r", "<br/>")

    def get_context_data(self, **kwargs):
        context = super(generic.ListView, self).get_context_data(**kwargs)

        if self.request.session['to_compute']:

            ###################################################################
            # BABA support

            baba = Parser.BABAProgramParser(string=self.request.session['input']).parse()

            g_probabilities, s_probabilities, i_probabilities = Semantics.compute_semantic_probabilities(baba)
            context['g_probabilities'] = g_probabilities
            context['s_probabilities'] = s_probabilities
            context['i_probabilities'] = i_probabilities

            random_variables = [rv.symbol for rv in baba.random_variables]
            context['random_variables'] = random_variables

            baba_worlds_formset = formset_factory(BabaWorldForm, extra=0)

            random_variable_world = []
            if 'world_definition' in self.request.session:
                world_definition = self.request.session['world_definition']

                random_variable_elements = list([rv for rv in baba.random_variables])
                rv_world = [elem['select'] == '0' for elem in world_definition]
                for i in range(len(rv_world)):
                    rv = random_variable_elements[i]
                    rv.negation = not rv_world[i]
                    random_variable_world.append(rv)

            else:
                world_definition = [{'select': 0} for _ in range(len(random_variables))]

            baba_worlds_formset = baba_worlds_formset(initial=world_definition)
            context['baba_worlds_formset'] = baba_worlds_formset

            for index, form in enumerate(baba_worlds_formset):
                form.data['world_label'] = random_variables[index]

            baba.set_random_variable_world(random_variable_world)
            framework_extension = babaUtilities.compute_framework_extension(random_variable_world)

            admissibles = Semantics.generate_admissible(baba)
            stable_extensions = Semantics.stable(baba, admissibles)
            grounded_extensions = Semantics.grounded(baba, admissibles)
            complete_extensions = Semantics.complete(baba, admissibles)
            preferred_extensions = Semantics.preferred(baba, admissibles)
            ideal_extensions = Semantics.ideal(baba, admissibles)

            stable_derivable = [(s, Semantics.derivable_set(baba, s.elements)) for s in stable_extensions]
            grounded_derivable = [(s, Semantics.derivable_set(baba, s.elements)) for s in grounded_extensions]
            complete_derivable = [(s, Semantics.derivable_set(baba, s.elements)) for s in complete_extensions]
            preferred_derivable = [(s, Semantics.derivable_set(baba, s.elements)) for s in preferred_extensions]
            ideal_derivable = [(s, Semantics.derivable_set(baba, s.elements)) for s in ideal_extensions]

            stable_sets = SemanticsUtils.extensions_and_derivations_to_str_list(stable_derivable)
            grounded_sets = SemanticsUtils.extensions_and_derivations_to_str_list(grounded_derivable)
            complete_sets = SemanticsUtils.extensions_and_derivations_to_str_list(complete_derivable)
            preferred_sets = SemanticsUtils.extensions_and_derivations_to_str_list(preferred_derivable)
            ideal_sets = SemanticsUtils.extensions_and_derivations_to_str_list(ideal_derivable)

            context['stable_sets'] = stable_sets
            context['grounded_sets'] = grounded_sets
            context['complete_sets'] = complete_sets
            context['preferred_sets'] = preferred_sets
            context['ideal_sets'] = ideal_sets

            ###################################################################

            rules_added = None
            framework_input = self.request.session['input']
            framework_to_parse = framework_input + framework_extension
            res = generate_aba_plus_framework(framework_to_parse)

            abap = res[0]
            #reverse dictionary to map sentences to contraries
            contr_map = dict((v, k) for k, v in res[1].items())
            if self.request.session['auto_WCP']:
                rules_added = rules_to_str(abap.check_or_auto_WCP(auto_WCP=True), contr_map)
                context['rules_added'] = rules_added
            else:
                abap.check_or_auto_WCP()

            res = abap.generate_arguments_and_attacks_for_contraries()
            attacks = res[1]
            deductions = res[2]

            set_attacks = convert_to_attacks_between_sets(res[1])
            context['attacks'] = [set_atk_to_str(atk) for atk in set_attacks]

            asp = ASPARTIX_Interface(abap)
            asp.generate_input_file_for_clingo(SOLVER_INPUT)

            stable_ext = asp.calculate_stable_arguments_extensions(SOLVER_INPUT)
            grounded_ext = asp.calculate_grounded_arguments_extensions(SOLVER_INPUT)
            complete_ext = asp.calculate_complete_arguments_extensions(SOLVER_INPUT)
            preferred_ext = asp.calculate_preferred_arguments_extensions(SOLVER_INPUT)
            ideal_ext = {} #asp.calculate_ideal_arguments_extensions(SOLVER_INPUT)

            context['stable'] = arguments_extensions_to_str_list(stable_ext, contr_map)
            context['grounded'] = arguments_extensions_to_str_list(grounded_ext, contr_map)
            context['complete'] = arguments_extensions_to_str_list(complete_ext, contr_map)
            context['preferred'] = arguments_extensions_to_str_list(preferred_ext, contr_map)
            context['ideal'] = arguments_extensions_to_str_list(ideal_ext, contr_map)

            # maps indices to extensions
            extension_map = {}
            i = 1
            for ext, conclusions in stable_ext.items():
                extension_map[i] = (ext, conclusions, STABLE)
                i += 1
            for ext, conclusions in grounded_ext.items():
                extension_map[i] = (ext, conclusions, GROUNDED)
                i += 1
            for ext, conclusions in complete_ext.items():
                extension_map[i] = (ext, conclusions, COMPLETE)
                i += 1
            for ext, conclusions in preferred_ext.items():
                extension_map[i] = (ext, conclusions, PREFERRED)
                i += 1
            for ext, conclusions in ideal_ext.items():
                extension_map[i] = (ext, conclusions, IDEAL)
                i += 1
            context['extensions'] = extension_map

            context['json_input'] = generate_json(deductions, attacks, None)

            context['input_text'] = self.request.session['input']

            self.request.session['to_compute'] = False
            self.request.session['highlight_index'] = None
            self.request.session['compare_index'] = None

            results[self.request.session.session_key] = {'abap': abap, 'deductions': deductions, 'attacks': attacks,
                                                         'contr_map': contr_map, 'extension_map': extension_map,
                                                         'stable_ext': stable_ext,
                                                         'grounded_ext': grounded_ext, 'complete_ext': complete_ext,
                                                         'ideal_ext': ideal_ext, 'preferred_ext': preferred_ext,
                                                         'rules_added': rules_added,
                                                         'g_probabilities': g_probabilities,
                                                         's_probabilities': s_probabilities,
                                                         'i_probabilities': i_probabilities,
                                                         'random_variables': random_variables,
                                                         'world_definition': world_definition,
                                                         'baba_worlds_formset': baba_worlds_formset,
                                                         'stable_sets': stable_sets, 'grounded_sets': grounded_sets,
                                                         'complete_sets': complete_sets, 'preferred_sets': preferred_sets,
                                                         'ideal_sets': ideal_sets}

        else:
            result = results[self.request.session.session_key]

            context['rules_added'] = result['rules_added']

            set_attacks = convert_to_attacks_between_sets(result['attacks'])
            context['attacks'] = [set_atk_to_str(atk) for atk in set_attacks]

            contr_map = result['contr_map']

            ###################################################################
            # BABA support

            context['stable'] = arguments_extensions_to_str_list(result['stable_ext'], contr_map)
            context['grounded'] = arguments_extensions_to_str_list(result['grounded_ext'], contr_map)
            context['complete'] = arguments_extensions_to_str_list(result['complete_ext'], contr_map)
            context['preferred'] = arguments_extensions_to_str_list(result['preferred_ext'], contr_map)
            context['ideal'] = arguments_extensions_to_str_list(result['ideal_ext'], contr_map)

            context['g_probabilities'] = result['g_probabilities']
            context['s_probabilities'] = result['s_probabilities']
            context['i_probabilities'] = result['i_probabilities']

            context['random_variables'] = result['random_variables']

            baba_worlds_formset = formset_factory(BabaWorldForm, extra=0)
            baba_worlds_formset = baba_worlds_formset(initial=result['world_definition'])
            context['baba_worlds_formset'] = baba_worlds_formset

            ###################################################################

            highlighted_ext = None
            if self.request.session['highlight_index']:
                extension_map = result['extension_map']
                to_highlight = self.request.session['highlight_index']
                highlighted_ext = extension_map[to_highlight][0]

                context['highlighted_extension'] = argument_to_str(extension_map[to_highlight][0],
                                                                   extension_map[to_highlight][1], contr_map)
                extension_type = extension_map[to_highlight][2]
                context['highlighted_extension_type'] = extension_type_names[extension_type]

            context['json_input'] = generate_json(result['deductions'], result['attacks'], highlighted_ext)

            if self.request.session['compare_index']:
                extension_map = result['extension_map']
                to_highlight = self.request.session['compare_index']
                highlighted_ext2 = extension_map[to_highlight][0]

                context['compared_extension'] = argument_to_str(extension_map[to_highlight][0],
                                                                   extension_map[to_highlight][1], contr_map)
                extension_type = extension_map[to_highlight][2]
                context['compared_extension_type'] = extension_type_names[extension_type]

                context['render_graph2'] = True
                context['json_input2'] = generate_json(result['deductions'], result['attacks'], highlighted_ext2)

            context['extensions'] = result['extension_map']
            context['input_text'] = self.request.session['input']

        return context

    def post(self, request, **kwargs):

        if "set_world" in request.POST:
            baba_worlds_formset = formset_factory(BabaWorldForm)
            baba_worlds_formset = baba_worlds_formset(request.POST)
            if baba_worlds_formset.is_valid():
                request.session['world_definition'] = baba_worlds_formset.cleaned_data
                request.session['to_compute'] = True
        else:
            if 'world_definition' in request.session:
                del request.session['world_definition']

        if "submit_text" in request.POST:
            request.session['input'] = request.POST['input_text']

            request.session['to_compute'] = True
            request.session['auto_WCP'] = False

        elif "submit_file" in request.POST:
            file = request.FILES['myfile']
            str = ""
            for chunk in file.chunks():
                str += chunk.decode("utf-8")
            request.session['input'] = str

            request.session['to_compute'] = True
            request.session['auto_WCP'] = False

        if 'auto_WCP' in self.request.POST:
            self.request.session['auto_WCP'] = True

        elif 'select_extension' in self.request.POST:
            selection = request.POST['select_extension']
            self.request.session['highlight_index'] = int(selection)

        elif 'compare_extension' in self.request.POST:
            selection = request.POST['compare_extension']
            self.request.session['compare_index'] = int(selection)

        return HttpResponseRedirect(reverse('aba_plus_django:results'))



def sets_to_str(sets, contr_map={}):
    """
    :param sets: set of sets of Sentences to format
    :param contr_map: dictionary mapping symbols of contraries to symbols of assumptions (default empty)
    :return: formatted string representation of sets
    """
    str = ""

    it = iter(sets)
    first_set = next(it, None)
    if first_set is not None:
        str += set_to_str(first_set, contr_map)
    for set in it:
        str += ", "
        str += set_to_str(set, contr_map)

    return str

def set_to_str(set, contr_map={}):
    """
    :param set: set of Sentences to format
    :param contr_map: dictionary mapping symbols of contraries to symbols of assumptions (default empty)
    :return: formatted string representation of sets
    """
    str = "{"

    it = iter(set)
    first_sentence = next(it, None)
    if first_sentence is not None:
        str += sentence_to_str(first_sentence, contr_map)
    for sentence in it:
        str += ", "
        str += sentence_to_str(sentence, contr_map)

    str += "}"

    return str

def sentence_to_str(sentence, contr_map={}):
    """
    :param sentence: Sentence to format
    :param contr_map: dictionary mapping symbols of contraries to symbols of assumptions (default empty)
    :return: formatted string representation of sentence
    """
    if sentence.is_contrary:
        if sentence.symbol in contr_map:
            return contr_map[sentence.symbol]
        return OVERLINE.format(sentence.symbol)
    else:
        return sentence.symbol

def set_atk_to_str(atk):
    """
    :param atk: tuple with 3 elements representing an attack between 2 sets:
                1: attacking set of Sentences
                2: attack type
                3: attacked set of Sentences
    :return: formatted string representation of atk
    """
    str = ""

    type = atk[2]
    if type == NORMAL_ATK:
        str = "Normal Attack: "
    elif type == REVERSE_ATK:
        str = "Reverse Attack: "

    str += set_to_str(atk[0])
    str += " {} ".format(R_ARROW)
    str += set_to_str(atk[1])

    return str

def arguments_extensions_to_str_list(extensions_dict, contr_map={}):
    """
    :param extensions_dict: dictionary mapping sets to their conclusions
    :param contr_map: dictionary mapping symbols of contraries to symbols of assumptions (default empty)
    :return: list of formatted arguments(deductions)
    """
    res = []

    for extension, conclusions in extensions_dict.items():
        res.append(argument_to_str(extension, conclusions, contr_map))

    return res

def argument_to_str(premise, conclusion, contr_map={}):
    """
    :param premise: set of Sentences representing the premise
    :param conclusion: set of Sentences representing the conclusion
    :param contr_map: dictionary mapping symbols of contraries to symbols of assumptions (default empty)
    :return: formatted argument(deduction)
    """
    str = ""
    str += set_to_str(premise)
    str += " {} ".format(TURNSTILE)
    str += set_to_str(conclusion, contr_map)
    return str

def rules_to_str(rules, contr_map):
    """
    :param rules: collection of Rules to format
    :param contr_map: dictionary mapping symbols of contraries to symbols of assumptions (default empty)
    :return: formatted string representation of rules
    """
    str = ""

    for rule in rules:
        str += rule_to_str(rule, contr_map)

    return str

def rule_to_str(rule, contr_map):
    """
    :param rule: Rule to format
    :param contr_map: dictionary mapping symbols of contraries to symbols of assumptions (default empty)
    :return: formatted string representation of rule
    """
    str = ""

    str += sentence_to_str(rule.consequent, contr_map)
    str += " {} ".format(L_ARROW)
    str += set_to_str(rule.antecedent)

    str += "<br/>"

    return str


def generate_json(deductions, attacks, highlighted_sentences):
    """
    generate a json file with nodes and links representing sets and attacks between them
    :param deductions: collection of Deductions whose premises are to be represented as nodes
    :param attacks: collection of Attacks to be represented as directed links
    :param highlighted_sentences: collection of Sentences to be highlighted
    :return: string containing the the json
    """
    output = {"nodes": list(), "links": list()}

    support_sets = []
    for ded in deductions:
        if ded.premise not in support_sets:
            support_sets.append(ded.premise)

            if not(highlighted_sentences is None):
                group = HIGHLIGHTED if frozenset(ded.premise).issubset(highlighted_sentences) else NOT_HIGHLIGHTED2
            else:
                group = NOT_HIGHLIGHTED1

            node = {"name": set_to_str(ded.premise),
                    "group": group}
            output["nodes"].append(node)

    # maps (attacker, attackee) to attack type
    attack_map = {}
    for atk in attacks:
        key = (frozenset(atk.attacker.premise), frozenset(atk.attackee.premise))
        if key not in attack_map:
            attack_map[key] = atk.type
        elif atk.type != attack_map[key]:
            attack_map[key] = BOTH_ATTACKS

    for k, v in attack_map.items():
        idx_attacker = support_sets.index(k[0])
        idx_attackee = support_sets.index(k[1])

        link = {"source": idx_attacker,
                "target": idx_attackee,
                "value": v}
        output["links"].append(link)

    return json.dumps(output)


