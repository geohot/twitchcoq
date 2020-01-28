#!/usr/bin/env python3

# 6 possible states
# 2 values
# 2 moves
# 6*2*2 = 24
# 24^10 possible for sigma(5, 2)

# See Tree Normal Form from Bra66

t0 = "B1L A1L C1R B1R A1L D1R A1L E1R H1L C0R".split(" ")

def run(t0, ms=-1):
  t = [0]*30000
  pos = 15000
  s = "A"

  cnt = 0
  halt = True
  while 1:
    assert pos > 0
    assert pos < len(t)
    #if cnt%1000 == 0:
    #  print(cnt, s, pos)
    ns = ord(s) - ord("A")
    if t[pos] == 0:
      tt = t0[ns*2+0]
    elif t[pos] == 1:
      tt = t0[ns*2+1]
    s = tt[0]
    t[pos] = int(tt[1])
    if tt[2] == "L":
      pos -= 1
    else:
      pos += 1
    if s == "H":
      break
    cnt += 1
    if ms != -1 and cnt > ms:
      halt = False
      break
  return halt, cnt, sum(t)

if __name__ == "__main__":
  print(run(t0))
