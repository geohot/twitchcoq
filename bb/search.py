#!/usr/bin/env python3

MS = 2

mss = -1
mst = -1

def run(M, s, t, h, steps):
  global mss, mst
  # step count or head escape to end
  while steps < 200 and h > 1 and h < len(t)-1:

    # state adder, kick off with recursion
    if s not in M:
      #print("missing", s)
      for w in [0, 1]:
        for d in ['l', 'r']:
          nsp = [k[0] for k in M]
          if len(nsp) < MS:
            nsp.append(chr(ord('a')+len(nsp)))
          else:
            nsp.append('H')
          for ns in nsp:
            # copy M and t here, and kick off all the new machines
            Mp = M.copy()
            Mp[s] = (w,d,ns)
            run(Mp, s, t[:], h, steps)
      return

    # s in M
    w,d,ns = M[s]

    # update the tape and head position
    t[h] = w
    if d == 'l':
      h -= 1
    else:
      h += 1

    s = (ns, t[h])
    steps += 1

    # check for halt
    if s[0] == 'H':
      mss = max(steps, mss)
      mst = max(sum(t), mst)
      print("halt", steps, sum(t), mss, mst)
      break
    


t = [0]*1000
M = {}
M[('a', 0)] = (1, 'r', 'b')
run(M, ('a', 0), t, 500, 0)
print(mss, mst)



