#!/usr/bin/env python3

from lark import Lark

l = Lark(open("grammar.g").read())
p = l.parse(open("stl/peano.v").read())

def handle_inductive(x):
  xx = x.children[0]
  print(dir(xx))
  print(xx)
  print(xx.pretty())

def handle_definition(x):
  pass

def handle_assertion(x):
  pass


for x in p.children:
  xx = x.children[0]  # skip sentence
  print(xx.pretty())
  """
  stype = xx.data
  if stype == "inductive":
    handle_inductive(xx)
    exit(0)
  if stype == "definition":
    handle_definition(xx)
  if stype == "assertion":
    handle_assertion(xx)
  """



