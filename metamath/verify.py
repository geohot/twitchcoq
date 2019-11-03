#!/usr/bin/env python3
import sys
import code
from lark import Lark

l = Lark(open("mm.g").read(), parser="lalr")
p = l.parse(open("miu2.mm" if len(sys.argv)==1 else sys.argv[1]).read())
print("*********** LOADED ***********")

class Scope(object):
  def __init__(self):
    self.constants = set()
    self.asserts = dict()
    self.hypos = dict()
    self.variables = dict()
    self.essen = list()

  def child(self):
    ret = Scope()
    # asserts are noscope
    ret.asserts = self.asserts

    ret.constants = self.constants.copy()
    ret.variables = self.variables.copy()

    ret.hypos = self.hypos.copy()
    ret.essen = self.essen.copy()

    return ret

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

def verify_proof(scope, intyc, inms, xx):
  xx = xx.children[0]
  assert xx.data == "uncompressed_proof"

  stack = Stack()
  for s in xx.children:
    bindings = {}
    def bind(ms):
      nms = []
      for v in ms[::-1]:
        if v in scope.variables:
          if v not in bindings:
            vt, vnms = stack.pop()
            assert 'type' in scope.variables[v]
            assert scope.variables[v]['type'] == vt
            if 'disjoint' in scope.variables[v]:
              # TODO: check for disjoint
              # is it here, am i understanding right?
              pass
            print("  bind %s to %s" % (v, lp(vnms)))
            bindings[v] = vnms
          nms.append(bindings[v])
        else:
          # pass through constants
          assert v in scope.constants
          nms.append([v])
      ret = []
      for x in nms[::-1]:
        ret += x
      return ret

    if s in scope.asserts:
      a = scope.asserts[s]
      ms = a['ms']
      # first bind in essential scope
      pop = []
      for e in a['scope'].essen[::-1]:
        et, enms = stack.pop()
        assert e['type'] == et
        print("%s: must verify %s %s is %s %s" % (e['lbl'], e['type'], lp(e['ms']), et, lp(enms)))
        pop.append((et, enms, e['ms'], e['lbl']))
      for et, enms, ems, lbl in pop:
        print("working on %s" % lbl)
        nms = bind(ems)
        print("compare %s to %s" % (lp(nms), lp(enms)))
        assert nms == enms
      nms = bind(ms)
      stack.push(a['type'], nms)
    elif s in scope.hypos:
      a = scope.hypos[s]
      # don't bind variables
      stack.push(a['type'], a['ms'])
    else:
      raise Exception("%s label not found" % s)


  # confirm stack is this
  o = stack.pop()
  print("  produced %s %s expected %s %s" % (o[0], lp(o[1]), intyc, lp(inms)))
  assert(len(stack) == 0)
  assert o == (intyc, inms)

def parse_stmt(scope, xx):
  if xx.data == "variable_stmt":
    for y in xx.children:
      vname = y.children[0]
      assert vname not in scope.variables
      scope.variables[vname] = {}
  elif xx.data == "hypothesis_stmt":
    xx = xx.children[0]
    lbl = xx.children[0]
    tyc = xx.children[1].children[0].children[0]
    assert tyc in scope.constants
    if xx.data == "floating_stmt":
      var = xx.children[2].children[0]
      assert var in scope.variables
      # TODO: we are throwing away this name, do we need it?
      assert 'type' not in scope.variables[var]
      scope.variables[var]['type'] = tyc
      scope.hypos[lbl] = {"type": tyc, "ms": [var]}
    elif xx.data == "essential_stmt":
      ms = xx.children[2:]
      scope.essen.append({"type": tyc, "ms": ms, "lbl": lbl})
      scope.hypos[lbl] = {"type": tyc, "ms": ms}
  elif xx.data == "assert_stmt":
    xx = xx.children[0]
    lbl = xx.children[0]
    tyc = xx.children[1].children[0].children[0]
    assert tyc in scope.constants
    if xx.data == "axiom_stmt":
      ms = xx.children[2:]
      proof = None
    elif xx.data == "provable_stmt":
      ms = xx.children[2:-1]
      proof = xx.children[-1]
      """
      print("verifying proof for %s" % lbl)
      verify_proof(scope, tyc, ms, proof)
      print("verified proof for %s" % lbl)
      """
    scope.asserts[lbl] = {'type': tyc, 'ms': ms, 'scope': scope, 'proof': proof}
  elif xx.data == "disjoint_stmt":
    av = [x.children[0] for x in xx.children]
    for v in av:
      assert v in scope.variables
      scope.variables[v]['disjoint'] = [x for x in av if x != v]
  elif xx.data == "block":
    tscope = scope.child()
    for y in xx.children:
      parse_stmt(tscope, y.children[0])
  else:
    print("IMPLEMENT", xx.data)
    pass

scope = Scope()
for x in p.children:
  xx = x.children[0]
  if xx.data == "constant_stmt":
    for y in xx.children:
      cname = y.children[0]
      assert cname not in scope.constants
      scope.constants.add(cname)
  else:
    xx = xx.children[0]
    parse_stmt(scope, xx)

print("*********** PARSED ***********")
for k,v in scope.asserts.items():
  if v['proof'] is not None:
    print("******** verify %s" % k)
    verify_proof(v['scope'], v['type'], v['ms'], v['proof'])
print("*********** VERIFIED ***********")

