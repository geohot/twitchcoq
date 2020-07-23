// (State, Input, Output, Direction, NewState)
#include <vector>

#define N 5
#define M 2

#define S(x) (x-'a')
#define D(x) (x == 'r' ? 1 : -1)

class transition {
public:
  transition() {
    output = 0;
    direction = D('l');
    new_state = -1;
  }
  transition(int o, int d, int ns) :
    output(o), direction(d), new_state(ns)
  {
  }

  int output;
  int direction;
  // halt state is -1
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

  std::vector<int> fwd;
  std::vector<int> bwd;
};

void generate() {
  transition tf[N][M];

  // step 1
  tf[S('a')][0] = transition(1, D('r'), S('b'));

  // step 2 (eight choices)
  tf[S('b')][0] = transition(0, D('l'), S('a'));
  tf[S('b')][0] = transition(1, D('l'), S('a'));

  tf[S('b')][0] = transition(0, D('l'), S('b'));
  tf[S('b')][0] = transition(1, D('l'), S('b'));

  tf[S('b')][0] = transition(0, D('l'), S('c'));
  tf[S('b')][0] = transition(1, D('l'), S('c'));

  tf[S('b')][0] = transition(0, D('r'), S('c'));
  tf[S('b')][0] = transition(1, D('r'), S('c'));

  // step 3

}


int main() {
  tape t;
  printf("%d\n", t[0]);
  t[55] = 1;
  printf("%d\n", t[55]);
  printf("%d\n", t[-55]);
  t[-55] = 1;
  printf("%d\n", t[-55]);

  //generate();
}


