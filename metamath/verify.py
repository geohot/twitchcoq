#!/usr/bin/env python3
import sys
import code
from lark import Lark

l = Lark(open("mm.g").read())
p = l.parse(open("miu2.mm" if len(sys.argv)==1 else sys.argv[1]).read())

constants = set()
asserts = dict()
hypos = dict()
variables = dict()
essen = dict()

def lp(ms):
  return ' '.join(map(str, ms))

class Stack(object):
  def __init__(self):
    self.ss = []

  def __len__(self):
    return len(self.ss)

  def push(self, tyc, ms):
    self.ss.append((tyc, ms))
    print("*** pushed", tyc, lp(ms))

  def pop(self):
    ret = self.ss.pop()
    print("*** popped", ret[0], lp(ret[1]))
    return ret

def verify_proof(intyc, inms, xx):
  xx = xx.children[0]
  stack = Stack()
  for s in xx.children:
    bindings = {}
    def bind(ms):
      # then bind in normal scope
      nms = []
      for v in ms[::-1]:
        if v in variables:
          if v not in bindings:
            vt, vnms = stack.pop()
            assert variables[v]['type'] == vt
            bindings[v] = vnms
          nms.append(bindings[v])
        else:
          # pass through constants
          nms.append([v])
      ret = []
      for x in nms[::-1]:
        ret += x
      return ret

    if s in asserts:
      a = asserts[s]
      ms = a['ms']
      # first bind in essential scope
      for e in a['essen'].values():
        et, enms = stack.pop()
        assert e['type'] == et
        print("must verify %s %s is %s %s" % (e['type'], lp(e['ms']), et, lp(enms)))
        nms = bind(e['ms'])
        print("compare %s to %s" % (lp(nms), lp(enms)))
        assert nms == enms

      nms = bind(ms)
      stack.push(a['type'], nms)
    elif s in hypos:
      a = hypos[s]
      # don't bind variables
      stack.push(a['type'], a['ms'])

  # confirm stack is this
  o = stack.pop()
  print("  produced %s %s expected %s %s" % (o[0], lp(o[1]), intyc, lp(inms)))
  assert(len(stack) == 0)
  assert o == (intyc, inms)

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
      # TODO: we are throwing away this name, do we need it?
      variables[var]['type'] = tyc
      hypos[lbl] = {"type": tyc, "ms": [var]}
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


