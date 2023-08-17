#  parse function definition from sygus result

from six.moves import cStringIO  # Py2-Py3 Compatibility

from pysmt.smtlib.parser import SmtLibParser


def FuncParser(smtfuncdef, arglist):
    # with open ,replace unsat
    # if unknown return None
    parser = SmtLibParser()
    funcdef = parser.get_script(cStringIO(smtfuncdef))
    fdefs = list(funcdef.filter_by_command_name("define-fun"))
    assert (len(fdefs) == 1)
    fdef = fdefs[0]
    assert (fdef.args[0] == 'INV')
    # check params_list (self.args[1])
    # print (fdef.args[1])
    # print (fdef.args[3])

    assert (len(fdef.args[1]) == len(arglist))

    expr = fdef.args[3].substitute(dict(zip(fdef.args[1], arglist)))
    return expr


if __name__ == '__main__':
    list1 = [1, 2, 3]
    list2 = ['a', 'b', 'c']
    print(dict(zip(list1, list2)))
    smtfuncdef = "(define-fun INV ((addr (_ BitVec 4)) (base (_ BitVec 4)) (cnt (_ BitVec 4))) Bool (= cnt (_ bv1 4)))"
    FuncParser(smtfuncdef)
