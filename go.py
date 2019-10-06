#!/usr/bin/env python3

from lark import Lark

l = Lark(open("grammar.g").read())
p = l.parse(open("stl/peano.v").read())

for x in p.children:
  print(x.pretty())
  break

