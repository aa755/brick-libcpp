#include<memory>

std::shared_ptr<int> testnew4() {
    auto x= std::shared_ptr<int>(new int);
    *x=1;
    return x;
  }

int * testnew() {
  int *x;
  x=new int;
  *x=1;
  return x;
}

int * testnew2() {
    int *x=new int[2];
    x[0]=1;
    x[1]=2;
    return x;
  }
