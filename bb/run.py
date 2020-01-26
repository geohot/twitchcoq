#!/usr/bin/env python

t0 = "B1L C1R A1L A1L H1L".split(" ")
t1 = "A1L B1R D1R E1R C0R".split(" ")

t = [0]*30000
pos = 15000
s = "A"

cnt = 0
while 1:
  assert pos > 0
  assert pos < len(t)
  if cnt%1000 == 0:
    print(cnt, s, pos)
  ns = ord(s) - ord("A")
  if t[pos] == 0:
    tt = t0[ns]
  elif t[pos] == 1:
    tt = t1[ns]
  s = tt[0]
  t[pos] = int(tt[1])
  if tt[2] == "L":
    pos -= 1
  else:
    pos += 1
  if s == "H":
    break
  cnt += 1

print(sum(t))
