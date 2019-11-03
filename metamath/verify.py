#!/usr/bin/env python3
import code
from lark import Lark

l = Lark(open("mm.g").read())
p = l.parse(open("miu2.mm").read())

constants = set()
asserts = dict()
variables = dict()

for x in p.children:
  xx = x.children[0]
  if xx.data == "constant_stmt":
    for y in xx.children:
      cname = y
      assert cname not in constants
      constants.add(cname)
  else:
    xx = xx.children[0]
    if xx.data == "variable_stmt":
      for y in xx.children:
        vname = y
        assert vname not in variables
        variables[vname] = {}
    elif xx.data == "hypothesis_stmt":
      xx = xx.children[0]
      if xx.data == "floating_stmt":
        lbl = xx.children[0]
        tyc = xx.children[1].children[0]
        var = xx.children[2]
        assert tyc in constants
        assert var in variables
        variables[var]['type'] = tyc
        #code.interact(local=locals())
        #pass
      elif xx.data == "essential_stmt":
        # TODO: write this
        pass
    elif xx.data == "assert_stmt":
      xx = xx.children[0]
      if xx.data == "axiom_stmt":
        lbl = xx.children[0]
        tyc = xx.children[1].children[0]
        ms = xx.children[2:]
        asserts[lbl] = {'type': tyc, 'ms': ms}
      elif xx.data == "provable_stmt":
        lbl = xx.children[0]
        tyc = xx.children[1].children[0]
        ms = xx.children[2:-1]
        proof = xx.children[-1]
        asserts[lbl] = {'type': tyc, 'ms': ms}
      print(asserts[lbl])
      #print(xx.pretty())
    else:
      #print(xx.pretty())
      print(xx.data)
      pass

  #print(x.children[0].pretty())
print(constants)
print(variables)
print(asserts)

