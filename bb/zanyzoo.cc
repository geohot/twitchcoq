// (State, Input, Output, Direction, NewState)
#include <vector>
#include <queue>
using namespace std;

// total 2x2 -- 3*2*2*4 = 48

// for 2x3, we expect 2764
// for 3x2, we expect 3508

#define N 2
#define M 3

#define STATE_HALT -1
#define STATE_UNDEFINED -2

#define S(x) (x-'a')
#define D(x) (x == 'r' ? 1 : -1)

#define rS(x) (x == -1 ? 'h' : (x+'a'))
#define rD(x) (x == 1 ? 'r' : 'l')

class transition {
public:
  transition() {
    output = -1;
    direction = 0;
    new_state = -2;
  }
  transition(int o, int d, int ns) :
    output(o), direction(d), new_state(ns)
  {
  }

  int output;
  int direction;
  int new_state;
};

class tape {
public:
  int& operator[](int l) {
    if (l >= 0) {
      if (fwd.size() < (l+1)) { fwd.resize(l+1, 0); }
      return fwd.data()[l];
    } else {
      l = (-l)-1;
      if (bwd.size() < (l+1)) { bwd.resize(l+1, 0); }
      return bwd.data()[l];
    }
  }

  bool is_blank() {
    for (auto s : fwd) { if (s != 0) return false; }
    for (auto s : bwd) { if (s != 0) return false; }
    return true;
  }

  // these are copied when we copy the tape
  vector<int> fwd;
  vector<int> bwd;
};

class machine {
public:
  machine() {
    cs = S('a');
    cp = 0;
    steps = 0;
    card = 0;
    num_states = 0;
    num_symbols = 0;
  }

  void add_tf(int n, int m, int output, int direction, int new_state) {
    num_states = max(num_states, n+1);
    num_symbols = max(num_symbols, m+1);
    num_states = max(num_states, new_state+1);
    num_symbols = max(num_symbols, output+1);
    assert(new_state != STATE_UNDEFINED);
    card += (tf[n][m].new_state == STATE_UNDEFINED);

    tf[n][m].output = output;
    tf[n][m].direction = direction;
    tf[n][m].new_state = new_state;
  }

  bool is_full() {
    //printf("is_full %d %d\n", num_states, num_symbols);
    return (num_states == N && num_symbols == M);
  }

  void print() {
    for (int n = 0; n < N; n++) { 
      for (int m = 0; m < M; m++) { 
        if (tf[n][m].new_state == STATE_UNDEFINED) {
          printf("___ ");
        } else {
          printf("%d%c%c ", tf[n][m].output,
            rD(tf[n][m].direction),
            rS(tf[n][m].new_state));
        }
      }
    }
    printf("\n");
  }

  bool operator <(const machine& m) const {
    return steps > m.steps;
  }

  bool run() {
    steps++;
    transition &ttf = tf[cs][t[cp]];
    t[cp] = ttf.output;
    cp += ttf.direction;
    cs = ttf.new_state;
    return cs != STATE_HALT;
  }

  bool is_zdex() {
    bool ret = true;
    for (int n = 0; n < N; n++) {
      if (tf[n][0].new_state != STATE_UNDEFINED) {
        if (tf[n][0].direction != 1) { ret=false; break; }
      }
    }
    return ret;
  }

  int num_states;
  int num_symbols;
  int card;

  tape t;
  int cs;
  int cp;
  transition tf[N][M];
  int steps;
};

void generate() {
  machine mm;
  priority_queue<machine> ms;

  printf("init\n");
  // step 1
  mm.add_tf(S('a'), 0, 1, D('r'), S('b'));
  printf("step 1\n");

  // step 2 (eight choices)
  mm.add_tf(S('b'), 0, 0, D('l'), S('a')); ms.push(mm);
  mm.add_tf(S('b'), 0, 1, D('l'), S('a')); ms.push(mm);

  mm.add_tf(S('b'), 0, 0, D('l'), S('b')); ms.push(mm);
  mm.add_tf(S('b'), 0, 1, D('l'), S('b')); ms.push(mm);

  if (N >= 3) {
    mm.add_tf(S('b'), 0, 0, D('l'), S('c')); ms.push(mm);
    mm.add_tf(S('b'), 0, 1, D('l'), S('c')); ms.push(mm);

    mm.add_tf(S('b'), 0, 0, D('r'), S('c')); ms.push(mm);
    mm.add_tf(S('b'), 0, 1, D('r'), S('c')); ms.push(mm);
  }
  printf("step 2\n");

  /*printf("%lu\n", ms.size());
  while (ms.size() > 0) {
    mm = ms.top();
    ms.pop();
    printf("%d\n", mm.tf[S('b')][0].output);
  }
  exit(0);*/

  int bb_n = 0;
  vector<machine> halting;
  
  // step 3
  while (ms.size() > 0) {
    mm = ms.top();
    ms.pop();

    // failed blank tape
    if (mm.steps > 0 && mm.t.is_blank()) continue;

    transition &ttf = mm.tf[mm.cs][mm.t[mm.cp]];
    printf("%d %lu -- %lu %lu -- %d: %d %d=%d x out:%d dir:%d ns:%d\n", bb_n,
      1+halting.size()+ms.size(),
      halting.size(), ms.size(),
      mm.steps, mm.cs, mm.cp, mm.t[mm.cp],
      ttf.output, ttf.direction, ttf.new_state);

    // step 4: about to go to an undefined place!
    if (ttf.new_state == STATE_UNDEFINED) {
      // potentially add the halting state
      if (mm.is_full()) {
        // TODO: check "0-dextrous" from definition 23
        // add halt state and halt
        mm.add_tf(mm.cs, mm.t[mm.cp], 1, D('r'), STATE_HALT);
        if (!mm.is_zdex() && mm.steps > N) {
          halting.push_back(mm);
        }
      } 
      // add the other states
      for (int n = 0; n < N; n++) {
        for (int m = 0; m < M; m++) {
          for (int d : {-1, 1}) {
            mm.add_tf(mm.cs, mm.t[mm.cp], m, d, n);
            if (!mm.is_zdex()) {
              ms.push(mm);
            }
          }
        }
      }
      continue;
    }

    // step 5: 9 steps? halt with the 10th
    //printf("%d\n", mm.card());
    if (mm.card == N*M-1) {
      // add halting to the missing state
      for (int n = 0; n < min(mm.num_states+1, N); n++) {
        for (int m = 0; m < min(mm.num_symbols+1, M); m++) {
          if (mm.tf[n][m].new_state == STATE_UNDEFINED) {
            mm.add_tf(n, m, 1, D('r'), STATE_HALT);
            halting.push_back(mm);
          }
        }
      }
      continue;
    }

    // run step, add back to queue if no halt
    // more run please
    if (mm.run()) {
      ms.push(mm);
    } else {
      if (mm.steps > N) {
        halting.push_back(mm);
        bb_n = max(mm.steps, bb_n);
      }
    }
  }


  printf("looking at %lu machines\n", halting.size());
  for (auto h : halting) {
    h.print();
  }

}


int main() {
  // proof the tape is copied
  /*machine mm;
  mm.tf[S('a')][0] = transition(1, D('r'), S('b'));
  machine mm2 = mm;

  printf("%d %d\n", mm.steps, mm.t[0]);
  printf("%d %d\n", mm2.steps, mm2.t[0]);
  mm.run();
  printf("%d %d\n", mm.steps, mm.t[0]);
  printf("%d %d\n", mm2.steps, mm2.t[0]);*/

  generate();
}


