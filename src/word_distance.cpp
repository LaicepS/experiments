#include <string>
#include <vector>

#include "NamedType/named_type.hpp"
#include "range/v3/range.hpp"

using namespace std;
using namespace fluent;

namespace r = ranges;

using distance_t = NamedType<int, struct DistanceTag>;

distance_t word_distance(vector<string> &, string const &, string const &) {
  return distance_t(0);
}

int main() {
  string a = "a";
  string b = "b";
  vector<string> words;
  assert(distance_t(1).get() == word_distance(words, a, b).get());
  return 0;
}
