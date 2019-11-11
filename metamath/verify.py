#!/usr/bin/env python3
from __future__ import print_function
import os
import sys
import code
import lark
import logging
import argparse
import traceback
import itertools
from tqdm import tqdm

parser = argparse.ArgumentParser(description='Verify metamath')
parser.add_argument('-r', '--repl', action='store_true')
parser.add_argument('-v', '--verbose', action='store_true')
parser.add_argument('-d', '--debug', action='store_true')
parser.add_argument('file', type=str)
args = parser.parse_args()

logging.basicConfig(level=logging.WARNING, format='%(message)s')

log = logging.getLogger(__name__)
loglevel = logging.WARNING
if args.debug:
  loglevel = logging.DEBUG
elif args.verbose:
  loglevel = logging.INFO
log.setLevel(loglevel)

grammar = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "mm.g")).read()
l = lark.Lark(grammar, parser="lalr")
p = l.parse(open(args.file).read())
log.info("*********** LOADED ***********")

class Scope(object):
  def __init__(self):
    self.constants = set()
    self.asserts = dict()
    self.hypos = dict()
    self.variables = list()
    self.horder = list()
    self.vtypes = dict()
    self.disjoints = set()
    self.essen = list()

  def child(self):
    ret = Scope()
    # asserts are noscope
    ret.asserts = self.asserts

    ret.constants = self.constants.copy()
    ret.variables = self.variables[:]
    ret.horder = self.horder[:]
    ret.vtypes = self.vtypes.copy()
    ret.disjoints = self.disjoints.copy()

    ret.hypos = self.hypos.copy()
    ret.essen = self.essen[:]

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
    log.debug("*** pushed {} {}".format(tyc, lp(ms)))

  def pop(self):
    ret = self.ss.pop()
    log.debug("*** popped {} {}".format(ret[0], lp(ret[1])))
    return ret

  def peek(self):
    return self.ss[-1]

def variables_in_scope(scope, ms):
  tvars = []
  for e in scope.essen:
    for v in e['ms']:
      if v in scope.variables and v not in tvars:
        tvars.append(v)
  for v in ms:
    if v in scope.variables and v not in tvars:
      tvars.append(v)
  return sorted(tvars, key=lambda x: scope.horder.index(x))

def decompress_proof(scope, inms, children):
  crib = []
  for v in variables_in_scope(scope, inms):
    for lbl,kk in scope.hypos.items():
      if kk['ms'] == [v] and kk['floating']:
        if lbl not in crib:
          crib.append(lbl)

  # get essential hypothesis
  crib += [x['lbl'] for x in scope.essen]
  log.debug(lp(crib))

  # add to crib and parse weird numbers
  cc = []
  for x in children:
    if x.type == "LABEL":
      crib.append(x)
    else:
      assert x.type == "COMPRESSED_PROOF_BLOCK"
      cc.append(str(x))

  # parse weird numbers
  nn = []
  zz = []
  acc = 0
  for c in ''.join(cc):
    if c in 'UVWXY':
      acc *= 5
      acc += ord(c) - (ord('U')-1)
    elif c in 'ABCDEFGHIJKLMNOPQRST':
      acc *= 20
      acc += ord(c) - (ord('A')-1)
      nn.append(acc)
      acc = 0
    elif c == "Z":
      assert acc == 0
      zz.append(len(nn))
  #print(len(crib), len(zz))
  ret = []
  for n in nn:
    i = n-1
    if i < len(crib):
      ret.append(crib[i])
    elif i < len(crib)+len(zz):
      z = zz[i-len(crib)]
      ret.append(z)
    else:
      log.error("out of range {}".format(i))
      assert False
    #print(len(ret), n, ret[-1])
  return ret

def exec_metamath(scope, lbls):
  refs = []
  stack = Stack()
  for ii, s in enumerate(lbls):
    log.debug("  proof(%d) %s -> " % (ii+1, s))
    bindings = {}
    def do_bind(scope, v):
      if v not in bindings:
        vt, vnms = stack.pop()
        assert v in scope.vtypes
        if scope.vtypes[v] != vt:
          log.warning("  expected type %s, got type %s while binding %s to %s" % (scope.vtypes[v], vt, v, lp(vnms)))
        assert scope.vtypes[v] == vt
        log.debug("  bind %s to %s" % (v, lp(vnms)))
        bindings[v] = vnms

    def bind(scope, ms):
      nms = []
      for v in ms:
        if v in scope.variables:
          # late binding no longer supported
          assert v in bindings
          nms.append(bindings[v])
        else:
          # pass through constants
          if v not in scope.constants:
            log.warning("WTF", v, "ISN'T A CONSTANT", lp(ms))
          assert v in scope.constants
          nms.append([v])
      ret = []
      for x in nms:
        ret += x
      return ret

    if s in scope.asserts:
      a = scope.asserts[s]
      ms = a['ms']
      # first bind in essential scope
      pop = []

      for e in a['scope'].essen[::-1]:
        et, enms = stack.pop()
        log.debug("%s: must verify %s %s is %s %s" % (e['lbl'], e['type'], lp(e['ms']), et, lp(enms)))
        assert e['type'] == et
        pop.append((et, enms, e['ms'], e['lbl']))

      # early binding
      tvars = variables_in_scope(a['scope'], ms)
      log.debug("binding [%s]" % lp(tvars))
      for v in tvars[::-1]:
        do_bind(a['scope'], v)

      # verify disjoints
      for v1, v2 in a['scope'].disjoints:
        if v1 in bindings and v2 in bindings:
          for bvv1 in [x for x in bindings[v1] if x in a['scope'].variables]:
            for bvv2 in [x for x in bindings[v2] if x in a['scope'].variables]:
              # confirm bvv1 and bvv2 are disjoint in current scope
              log.debug("verify %s %s disjoint" % (bvv1, bvv2))
              assert bvv1 != bvv2
              assert (bvv1, bvv2) in scope.disjoints or \
                     (bvv2, bvv1) in scope.disjoints

      # parse essential
      for et, enms, ems, lbl in pop:
        log.debug("working on %s" % lbl)
        nms = bind(a['scope'], ems)
        log.debug("compare %s to %s" % (lp(nms), lp(enms)))
        assert nms == enms

      stack.push(a['type'], bind(a['scope'], ms))
    elif s in scope.hypos:
      a = scope.hypos[s]
      # don't bind variables
      stack.push(a['type'], a['ms'])
    elif type(s) == int:
      oot, ooms = refs[s-1]
      log.debug("load ref", s, oot, lp(ooms))
      stack.push(oot, ooms)
    else:
      raise Exception("%s label not found" % s)
    refs.append(stack.peek())

  # confirm stack is this
  return stack

def parse_stmt(scope, xx):
  if xx.data == "variable_stmt":
    for y in xx.children:
      vname = y.children[0]
      assert vname not in scope.variables
      scope.variables.append(vname)
  elif xx.data == "hypothesis_stmt":
    xx = xx.children[0]
    lbl = xx.children[0]
    tyc = xx.children[1].children[0].children[0]
    assert tyc in scope.constants
    if xx.data == "floating_stmt":
      var = xx.children[2].children[0]
      assert var in scope.variables
      # TODO: we are throwing away this name, do we need it?
      assert var not in scope.vtypes
      scope.vtypes[var] = tyc
      scope.hypos[lbl] = {"type": tyc, "ms": [var], "floating": True}
      scope.horder.append(var)
    elif xx.data == "essential_stmt":
      ms = xx.children[2:]
      scope.essen.append({"type": tyc, "ms": ms, "lbl": lbl})
      scope.hypos[lbl] = {"type": tyc, "ms": ms, "floating": False}
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
    scope.asserts[lbl] = {'type': tyc, 'ms': ms, 'scope': scope.child(), 'proof': proof}
  elif xx.data == "disjoint_stmt":
    # if we don't check this, it should still verify, just sometimes wrongly
    av = [x.children[0] for x in xx.children]
    for v1 in av:
      assert v1 in scope.variables
      for v2 in av:
        if v1 != v2 and (v1,v2) not in scope.disjoints and (v2,v1) not in scope.disjoints:
          scope.disjoints.add((v1, v2))
  elif xx.data == "block":
    tscope = scope.child()
    for y in xx.children:
      parse_stmt(tscope, y.children[0])
  else:
    log.error("IMPLEMENT", xx.data)
    pass

scope = Scope()

def parse(p):
  for x in p.children:
    xx = x.children[0]
    if xx.data == "constant_stmt":
      for y in xx.children:
        cname = y.children[0]
        assert cname not in scope.constants
        scope.constants.add(cname)
    elif xx.data == "include_stmt":
      fn = str(xx.children[0])
      log.info("including %s" % fn)
      parse(l.parse(open(fn).read()))
    else:
      parse_stmt(scope, xx.children[0])
parse(p)

log.info("*********** PARSED ***********")
pbar = tqdm(scope.asserts.items())
for k,v in pbar:
  if v['proof'] is not None:
    pbar.set_description(k)
    log.info("******** verify %s" % k)

    # get proof labels
    xx = v['proof'].children[0]
    if xx.data == "compressed_proof":
      lbls = decompress_proof(v['scope'], v['ms'], xx.children)
    else:
      lbls = xx.children
    log.info(lp(lbls))
    stack = exec_metamath(v['scope'], lbls)
    o = stack.pop()
    assert len(stack) == 0
    log.info("  produced %s %s expected %s %s" % (o[0], lp(o[1]), v['type'], lp(v['ms'])))
    assert o == (v['type'], v['ms'])
log.info("*********** VERIFIED ***********")

def search_forward(scope, ty, ms):
  print("asserts: %d hypos: %d" % (len(scope.asserts), len(scope.hypos)))
  all_lbls = [lark.lexer.Token(value=x, type_="LABEL") for x in list(scope.asserts.keys())+list(scope.hypos.keys())]
  ok = [[],]
  d = 0
  while 1:
    d += 1
    print("searching at depth %d with %d" % (d, len(ok)))
    for prefix in ok[:]:
      for l in all_lbls:
        try:
          log.setLevel(logging.ERROR)
          x = prefix+[l]
          stack = exec_metamath(scope, x)
          log.setLevel(loglevel)
          o = stack.pop()
          if o[0] == ty and o[1] == ms:
            print("HIT", lp(x))
            return
          ok.append(x)
        except Exception:
          #traceback.print_exc()
          pass

def can_produce(scope, tms, ms, d):
  var = variables_in_scope(scope, tms)
  #print("CAN", lp(tms), "PRODUCE", lp(ms), "REPLACING", lp(var))
  p0, p1 = 0, 0
  binds = {}
  while p0 < len(tms) and p1 < len(ms):
    if tms[p0] not in var:
      if tms[p0] == ms[p1]:
        p0 += 1
        p1 += 1
      else:
        return None
    elif tms[p0] in binds:
      b = binds[tms[p0]]
      if b[1] == ms[p1:p1+len(b[1])]:
        p0 += 1
        p1 += len(b[1])
      else:
        return None
    else:
      # tms[p0] is a var
      # 1 symbol replaced for now
      # this is an issue
      for l in range(1, len(ms)-p1+1):
        if tms[p0] not in binds:
          qret = search(scope, scope.vtypes[tms[p0]], ms[p1:p1+l], d+1)
          if qret is not None:
            binds[tms[p0]] = (scope.vtypes[tms[p0]], ms[p1:p1+l], qret)
            p0 += 1
            p1 += l
            break
      else:
        return None
  if p0 != len(tms) or p1 != len(ms):
    return None
  return binds

def search(scope, ty, ms, d=0):
  if d == 10:
    return None
  print("  "*d+"searching for", ty, lp(ms))
  for k,x in scope.hypos.items():
    # hypothesis must be exact
    if x['type'] == ty and x['ms'] == ms:
      # exact match ends the search
      return [k]

  for k,x in scope.asserts.items():
    if x['type'] == ty:
      binds = can_produce(scope, x['ms'], ms, d)
      if binds is not None:
        # get the order right
        var = variables_in_scope(scope, x['ms'])
        good = True
        rret = []
        for kk in var:
          if kk not in binds:
            good = False
            break
          rret += binds[kk][2]
        if good:
          return rret+[k]

  return None

def tokenize(ind, type_):
  return [lark.lexer.Token(value=x, type_=type_) for x in ind.split(" ")]

"""
#ms = tokenize("wff not = 0 S x", "MATH_SYMBOL")
#ms = tokenize("wff not = 0 S t", "MATH_SYMBOL")
ms = tokenize("wff = 0 0", "MATH_SYMBOL")
#ms = tokenize("|- = 0 0", "MATH_SYMBOL")
#ms = tokenize("term x", "MATH_SYMBOL")
#ms = tokenize("var x", "MATH_SYMBOL")
ret = search(scope, ms[0], ms[1:])
print(lp(ret))
t = exec_metamath(scope, ret).pop()
print(t[0], lp(t[1]))
"""

if args.repl:
  print("entering repl")
  # labels
  print("asserts:", lp(scope.asserts))
  print("hypos:", lp(scope.hypos))
  # math symbols
  print("constants:", lp(scope.constants))
  print("variables:", lp(scope.variables))
  try:
    import readline
  except ImportError:
    pass
  else:
    import rlcompleter
    readline.parse_and_bind("tab: complete")

  while True:
    ind = input('cmd> ').strip()
    if len(ind) == 0 or " " not in ind:
      continue
    cmd, ind = ind.split(" ", 1)
    if cmd == "c" or cmd == "command":
      lbls = tokenize(ind, "LABEL")
      try:
        stack = exec_metamath(scope, lbls)
        while len(stack) != 0:
          o = stack.pop()
          print(o[0], lp(o[1]))
      except Exception:
        traceback.print_exc()
    elif cmd == "s" or cmd == "search":
      # search for a set of labels that produces this string of math symbols
      ms = tokenize(ind, "MATH_SYMBOL")
      try:
        ret = search(scope, ms[0], ms[1:])
        if ret is not None:
          print(lp(ret))
        else:
          print("search failed")
      except KeyboardInterrupt:
        print("interrupted")
        pass


