#!/usr/bin/env python3
import code
from lark import Lark

l = Lark(open("mm.g").read())
p = l.parse(open("miu2.mm").read())

constants = set()
asserts = dict()
variables = dict()
essen = dict()

def verify_proof(tyc, ms, xx):
  xx = xx.children[0]
  for s in xx.children:
    assert s in asserts
    a = asserts[s]
    print(a)
  print(tyc, ms)

def parse_stmt(xx):
  if xx.data == "variable_stmt":
    for y in xx.children:
      vname = y.children[0]
      assert vname not in variables
      variables[vname] = {}
  elif xx.data == "hypothesis_stmt":
    xx = xx.children[0]
    lbl = xx.children[0]
    tyc = xx.children[1].children[0].children[0]
    assert tyc in constants
    if xx.data == "floating_stmt":
      var = xx.children[2].children[0]
      assert var in variables
      variables[var]['type'] = tyc
      #code.interact(local=locals())
      #pass
    elif xx.data == "essential_stmt":
      ms = xx.children[2:]
      essen[lbl] = {"type": tyc, "ms": ms}
  elif xx.data == "assert_stmt":
    xx = xx.children[0]
    lbl = xx.children[0]
    tyc = xx.children[1].children[0].children[0]
    assert tyc in constants
    if xx.data == "axiom_stmt":
      ms = xx.children[2:]
      asserts[lbl] = {'type': tyc, 'ms': ms, 'essen': essen.copy()}
    elif xx.data == "provable_stmt":
      ms = xx.children[2:-1]
      proof = xx.children[-1]
      verify_proof(tyc, ms, proof)
      asserts[lbl] = {'type': tyc, 'ms': ms}
    #print(asserts[lbl])
    #print(xx.pretty())
  else:
    #print(xx.pretty())
    print(xx.data)
    pass


for x in p.children:
  xx = x.children[0]
  if xx.data == "constant_stmt":
    for y in xx.children:
      cname = y.children[0]
      assert cname not in constants
      constants.add(cname)
  else:
    xx = xx.children[0]
    if xx.data == "block":
      # TODO: scoping
      for y in xx.children:
        parse_stmt(y.children[0])
      # reset essential statements
      # TODO: other scoping
      essen = dict()
    else:
      parse_stmt(xx)

  #print(x.children[0].pretty())

print("*********** PARSED ***********")
print(constants)
print(variables)
for k,v in asserts.items():
  print(k,v)


