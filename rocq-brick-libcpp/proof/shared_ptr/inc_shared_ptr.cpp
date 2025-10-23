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
