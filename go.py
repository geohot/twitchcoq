#!/usr/bin/env python3

from lark import Lark

l = Lark(open("grammar.g").read())

tmp = l.parse(open("stl/peano.v").read())
print(tmp)

