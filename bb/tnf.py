#!/usr/bin/env python3

# https://sci-hub.tw/10.1109/PGEC.1966.264572
# Hmm, the tree normal form description is kind of annoying, it's a graph, right?
# Oh, "Attacking the Busy Beaver 5" has a clearer description
# Does the first move need to print a one?

# A0 = B1L looks like the default start in "Attacking the Busy Beaver 5"
# E0 | E1 = H1L is the final one

# They even seem to be reasoning about the machines while they generate them
# This is a little annoying as the function can only be computed in order

# Hmm https://arxiv.org/pdf/1610.03184.pdf

from run import run

# 4*2*2 = 16
# 16^6 possible for sigma(3, 2)

def gen(x,b=3):
  e = (b+1)*2*2
  ret = []
  for i in range(b*2):
    t = x%e
    ss = "L" if t%2 else "R"
    t //= 2
    ss = ("0" if t%2 else "1") + ss
    t //= 2
    if t==b:
      ss = "H" + ss
    else:
      ss = chr(ord("A") + t) + ss
    ret.append(ss)
    x //= e
  return ret

if __name__ == "__main__":
  b = 3
  all_s = 0
  all_sigma = 0
  for m in range(((b+1)*2*2)**(b*2)):
    mm = gen(m, b)
    halt, s, sigma = run(mm, ms=100)
    print(mm, halt, s, sigma, all_s, all_sigma)
    if halt:
      all_s = max(s, all_s)
      all_sigma = max(sigma, all_sigma)




