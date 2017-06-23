def compute_framework_extension(rv_world):
    framework_extension = ''
    for rv in rv_world:
        if not rv.negation:
            framework_extension += '\nmyRule(' + rv.symbol + ', []).'

    return framework_extension
