from django import forms


class BabaWorldForm(forms.Form):
    select = forms.ChoiceField(widget=forms.RadioSelect, choices=[(0, 'TRUE'), (1, 'FALSE')])


class BabaWorldsForm(forms.Form):
    pass