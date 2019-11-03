#!/usr/bin/env python3
from lark import Lark

l = Lark(open("mm.g").read())
p = l.parse(open("miu2.mm").read())

for x in p.children:
  print(x.pretty())

