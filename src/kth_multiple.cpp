#include <cassert>
#include <functional>
#include <iostream>
#include <queue>
#include <unordered_set>

using namespace std;

struct unique_priority_queue {
  void insert(int elt) {
    if (elts.find(elt) == end(elts)) {
      elts.insert(elt);
      queue.push(elt);
    }
  }

  int pop() {
    auto top = queue.top();
    queue.pop();
    elts.erase(top);
    return top;
  }

 private:
  priority_queue<int, vector<int>, greater<int>> queue;
  unordered_set<int> elts;
};

int kth_multiple(int k) {
  int result;

  unique_priority_queue q;
  q.insert(1);
  for (int i = 0; i < k; i++) {
    result = q.pop();
    q.insert(result * 3);
    q.insert(result * 5);
    q.insert(result * 7);
  }

  return result;
}

int main() {
  assert(1 == kth_multiple(1));
  assert(3 == kth_multiple(2));
  assert(5 == kth_multiple(3));
  assert(7 == kth_multiple(4));
  assert(9 == kth_multiple(5));
  assert(15 == kth_multiple(6));
  assert(21 == kth_multiple(7));
  assert(25 == kth_multiple(8));
  assert(27 == kth_multiple(9));
  assert(35 == kth_multiple(10));
  assert(45 == kth_multiple(11));
  assert(49 == kth_multiple(12));
  return 0;
}
