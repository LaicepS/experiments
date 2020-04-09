#include <algorithm>
#include <cassert>
#include <string_view>
#include <iostream>
#include <unordered_map>
#include <unordered_set>

#include "NamedType/named_type.hpp"

using namespace std;

using Dict = unordered_set<string>;
using Cost = int;

using CacheKey = pair<size_t, string>;
using Cache = unordered_map<CacheKey, Cost>;

namespace std {

template <> struct hash<CacheKey> {

  size_t operator()(CacheKey const &p) const {
    return hash<size_t>()(p.first) ^ hash<string>()(p.second);
  }
};

} // namespace std

Cost cost(string const &word, Dict const &dict) {
  if (dict.find(word) != end(dict))
    return Cost(0);

  return Cost(word.size());
}

Cost respace(string_view const &text, size_t text_index,
             string const &curr_word, Dict const &dict, Cache &cache) {
  if (text_index == text.size())
    return cost(curr_word, dict);

  auto const cache_key = make_pair(text_index, curr_word);
  if (cache.find(cache_key) != end(cache))
    return cache[cache_key];

  auto const with_space = respace(text, text_index + 1, "", dict, cache);

  auto const new_word = curr_word + string(1, text[text_index]);
  auto const without_space =
      respace(text, text_index + 1, new_word, dict, cache);

  auto const best = min<Cost>(with_space + cost(new_word, dict), without_space);

  cache[cache_key] = best;
  return best;
}

int respace(string_view const &text, Dict const &dict) {
  if (text.size() == 0)
    return 0;

  Cache cache;

  return respace(text, 0, "", dict, cache);
}

int main() {
  assert(0 == respace("", {}));
  assert(1 == respace("f", {}));
  assert(0 == respace("f", {"f"}));
  assert(1 == respace("f", {"g"}));
  assert(2 == respace("fo", {}));
  assert(1 == respace("fo", {"o"}));
  assert(0 == respace("fo", {"f", "o"}));
  assert(2 == respace("fozu", {"f", "o"}));
  assert(4 ==
         respace("jesslooked", {"looked", "just", "like", "her", "brother"}));
  assert(7 == respace("jesslookedjustlikeherbrothertim",
                      {"looked", "just", "like", "her", "brother"}));
  return 0;
}
