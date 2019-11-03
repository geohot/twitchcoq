#!/usr/bin/env python3
import code
from lark import Lark

l = Lark(open("mm.g").read())
p = l.parse(open("miu2.mm").read())

constants = set()
asserts = dict()
variables = dict()
essen = dict()

def lp(ms):
  return ' '.join(map(str, ms))

class Stack(object):
  def __init__(self):
    self.ss = []

  def push(self, tyc, ms):
    self.ss.append((tyc, ms))
    print("*** pushed", tyc, lp(ms))

  def pop(self):
    ret = self.ss.pop()
    print("*** popped", ret[0], lp(ret[1]))
    return ret

def verify_proof(tyc, ms, xx):
  xx = xx.children[0]
  stack = Stack()
  for s in xx.children:
    assert s in asserts
    a = asserts[s]
    for e in a['essen'].values():
      print("must verify", e)
    stack.push(a['type'], a['ms'])

  # confirm stack is this
  o = stack.pop()
  print("  produced %s %s expected %s %s" % (o[0], lp(o[1]), tyc, lp(ms)))
  assert o == (tyc, ms)

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
      print("verifying proof for %s" % lbl)
      verify_proof(tyc, ms, proof)
      asserts[lbl] = {'type': tyc, 'ms': ms}
      print("verified proof for %s" % lbl)
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
"""
print(constants)
print(variables)
for k,v in asserts.items():
  print(k,v)
"""


