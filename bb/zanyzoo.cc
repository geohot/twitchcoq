// (State, Input, Output, Direction, NewState)
#include <vector>
#include <queue>

#define N 4
#define M 2

#define STATE_HALT -1
#define STATE_UNDEFINED -2

#define S(x) (x-'a')
#define D(x) (x == 'r' ? 1 : -1)

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

  /*tape& operator =(const tape& t) {
    // copy constructor on vector?
    fwd = t.fwd;
    bwd = t.bwd;
    return *this;
  }*/

  std::vector<int> fwd;
  std::vector<int> bwd;
};

class machine {
public:
  machine() {
    cs = S('a');
    cp = 0;
    steps = 0;
    // seen 'a' and 0
    state_seen[cs] = 1;
    symbol_seen[0] = 1;
  }

  /*machine& operator =(const machine& m) {
    printf("copy\n");
    cs = m.cs;
    cp = m.cp;
    steps = m.steps;
    for (int n = 0; n < N; n++) {
      for (int m = 0; m < M; m++) {
        tf[n][m] = m.tf[n][m];
      }
    }
    t = m.t;
    return *this;
  }*/

  bool operator <(const machine& m) const {
    return steps > m.steps;
  }

  int card() {
    int ret = 0;
    for (int n = 0; n < N; n++) { 
      for (int m = 0; m < M; m++) { 
        ret += (tf[n][m].new_state != STATE_UNDEFINED);
      }
    }
    return ret;
  }

  bool run() {
    steps++;
    transition &ttf = tf[cs][t[cp]];
    t[cp] = ttf.output;
    cp += ttf.direction;
    cs = ttf.new_state;
    if (cs >= 0) state_seen[cs] = 1;
    if (ttf.output >= 0) symbol_seen[ttf.output] = 1;
    return cs != STATE_HALT;
  }

  bool is_zdex() {
    bool ret=true;
    for (int n = 0; n < N; n++) {
      if (tf[n][0].new_state != STATE_UNDEFINED) {
        if (tf[n][0].direction != 1) { ret=false; break; }
      }
    }
    return ret;
  }

  bool is_full() {
    int states_seen = 0;
    int symbols_seen = 0;
    for (int n = 0; n < N; n++) { states_seen += state_seen[n]; }
    for (int m = 0; m < M; m++) { symbols_seen += symbol_seen[m]; }
    return states_seen == N && symbols_seen == M;
  }

  tape t;
  int cs;
  int cp;
  transition tf[N][M];
  int steps;

  int state_seen[N];
  int symbol_seen[M];
};

void generate() {
  machine mm;
  std::priority_queue<machine> ms;

  printf("init\n");
  // step 1
  mm.tf[S('a')][0] = transition(1, D('r'), S('b'));
  printf("step 1\n");

  // step 2 (eight choices)
  mm.tf[S('b')][0] = transition(0, D('l'), S('a')); ms.push(mm);
  mm.tf[S('b')][0] = transition(1, D('l'), S('a')); ms.push(mm);

  mm.tf[S('b')][0] = transition(0, D('l'), S('b')); ms.push(mm);
  mm.tf[S('b')][0] = transition(1, D('l'), S('b')); ms.push(mm);

  if (N >= 3) {
    mm.tf[S('b')][0] = transition(0, D('l'), S('c')); ms.push(mm);
    mm.tf[S('b')][0] = transition(1, D('l'), S('c')); ms.push(mm);

    mm.tf[S('b')][0] = transition(0, D('r'), S('c')); ms.push(mm);
    mm.tf[S('b')][0] = transition(1, D('r'), S('c')); ms.push(mm);
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
  std::vector<machine> halting;
  
  // step 3
  while (ms.size() > 0) {
    mm = ms.top();
    ms.pop();
    transition &ttf = mm.tf[mm.cs][mm.t[mm.cp]];
    printf("%d -- %lu %lu -- %d: %d %d=%d x %d %d %d\n", bb_n, halting.size(), ms.size(),
      mm.steps, mm.cs, mm.cp, mm.t[mm.cp],
      ttf.output, ttf.direction, ttf.new_state);

    // step 4: about to go to an undefined place!
    if (ttf.new_state == STATE_UNDEFINED) {
      // add back in, may generate all correct machines, just not run them
      // untested
      /*if (mm.is_full()) {
        // TODO: check "0-dextrous" from definition 23
        // add halt state and halt
        ttf.output = 1;
        ttf.direction = D('r');
        ttf.new_state = STATE_HALT;
        // will halt down below
      } else {*/
        for (int n = 0; n < N; n++) {
          for (int m = 0; m < M; m++) {
            for (int d : {-1, 1}) {
              ttf.output = m;
              ttf.direction = d;
              ttf.new_state = n;
              if (!mm.is_zdex()) {
                ms.push(mm);
              }
            }
          }
        }
        // no machine to run right now
        continue;
      //}
      //printf("UNDEFINED STATE!\n");
    }

    // step 5: 9 steps? halt with the 10th
    //printf("%d\n", mm.card());
    if (mm.card() == N*M-1) {
      // add halting to the missing state
      for (int n = 0; n < N; n++) {
        for (int m = 0; m < M; m++) {
          if (mm.tf[n][m].new_state == STATE_UNDEFINED) {
            mm.tf[n][m].output = 1;
            mm.tf[n][m].direction = D('r');
            mm.tf[n][m].new_state = STATE_HALT;
          }
        }
      }
    }

    // run step, add back to queue if no halt
    // more run please
    if (mm.run()) {
      ms.push(mm);
    } else {
      halting.push_back(mm);
      bb_n = std::max(mm.steps, bb_n);
    }
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


