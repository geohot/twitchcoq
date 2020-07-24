// (State, Input, Output, Direction, NewState)
#include <vector>
#include <queue>
#include <cassert>
#include <mutex>
#include <thread>
using std::vector;
using std::min;
using std::max;
using std::mutex;
using std::thread;
using std::priority_queue;

// total 2x2 -- 3*2*2*4 = 48

// for 2x3, we expect 2764
// for 3x2, we expect 3508 (228 for the first)
// for 4x2, we expect 511145, we get 637433

#define N 5
#define M 2

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

  bool will_go_undefined() {
    transition &ttf = tf[cs][t[cp]];
    return ttf.new_state == STATE_UNDEFINED;
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
    printf("%4d: ", steps);
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
    return cs == STATE_HALT;
  }

  /*bool is_zdex() {
    bool ret = true;
    for (int n = 0; n < N; n++) {
      if (tf[n][0].new_state != STATE_UNDEFINED) {
        if (tf[n][0].direction != 1) { ret=false; break; }
      }
    }
    return ret;
  }*/

  int num_states;
  int num_symbols;
  int card;

  tape t;
  int cs;
  int cp;
  transition tf[N][M];
  int steps;
};

// thread safe?
priority_queue<machine> ms;
vector<machine> out;
mutex mut;

void init() {
  machine mm;

  // step 1
  mm.add_tf(S('a'), 0, 1, D('r'), S('b'));

  /*mm.add_tf(S('b'), 0, 1, D('l'), S('a')); ms.push(mm);
  return;*/

  // step 2 (eight choices)
  for (int m = 0; m < min(mm.num_symbols+1, M); m++) {
    mm.add_tf(S('b'), 0, m, D('l'), S('a')); ms.push(mm);
    mm.add_tf(S('b'), 0, m, D('l'), S('b')); ms.push(mm);
  }

  if (N >= 3) {
    for (int m = 0; m < min(mm.num_symbols+1, M); m++) {
      mm.add_tf(S('b'), 0, m, D('l'), S('c')); ms.push(mm);
      mm.add_tf(S('b'), 0, m, D('r'), S('c')); ms.push(mm);
    }
  }
}

void add_queue(machine &mm) {
  mut.lock();
  ms.push(mm);
  mut.unlock();
}

void add_out(machine &mm) {
  mut.lock();
  out.push_back(mm);
  mut.unlock();
}

void generate() {
  machine mm;
  int bc = 0;

  // step 3
  while (true) {
    mut.lock();
    if (ms.size() == 0) {
      mut.unlock();
      break;
    }
    mm = ms.top();
    ms.pop();
    mut.unlock();

    // step 3: execute M on the blank input until...
    while (true) {
      if (bc % 10000 == 0) {
        transition &ttf = mm.tf[mm.cs][mm.t[mm.cp]];
        printf("%lu -- %lu %lu -- %d: %d %d=%d x out:%d dir:%d ns:%d\n",
          1+out.size()+ms.size(),
          out.size(), ms.size(),
          mm.steps, mm.cs, mm.cp, mm.t[mm.cp],
          ttf.output, ttf.direction, ttf.new_state);
      }
      bc++;

      // bound on number of exec steps exceeded
      if (mm.steps > 30) {
        add_out(mm);
        break;
      }

      // failed blank tape test, do not store or run
      if (mm.steps > 0 && mm.t.is_blank()) {
        //add_out(mm);
        break;
      } 

      // step 4: about to go to an undefined place! add possible branches
      if (mm.will_go_undefined()) {
        // potentially add the halting state
        if (mm.is_full()) {
          // TODO: check "0-dextrous" from definition 23
          // add halt state and halt
          mm.add_tf(mm.cs, mm.t[mm.cp], 1, D('r'), STATE_HALT);
          // this will terminate this step, just let it run
          add_queue(mm);
        } 
        // add the other states
        for (int n = 0; n < min(mm.num_states+1, N); n++) {
          for (int m = 0; m < min(mm.num_symbols+1, M); m++) {
            for (int d : {-1, 1}) {
              mm.add_tf(mm.cs, mm.t[mm.cp], m, d, n);
              add_queue(mm);
            }
          }
        }
        break;
      }

      // step 5: 9 steps? halt with the 10th
      if (mm.card == N*M-1) {
        // add halting to the missing state
        for (int n = 0; n < N; n++) {
          for (int m = 0; m < M; m++) {
            if (mm.tf[n][m].new_state == STATE_UNDEFINED) {
              mm.add_tf(n, m, 1, D('r'), STATE_HALT);
              // this is unknown if it halts, but it's complete
              add_out(mm);

              // don't return to main queue
              //add_queue(mm);
            }
          }
        }
        break;
      }

      if (mm.run()) {
        // halted
        add_out(mm);
        break;
      }
    }
  }
}

int main() {
  init();
  
  vector<thread*> tt;
  for (int i = 0; i < 1; i++) {
    tt.push_back(new thread(generate));
  }
  for (auto t : tt) {
    t->join();
  }

  printf("looking at %lu machines\n", out.size());
  /*for (auto mm : out) {
    mm.print();
  }*/
}


