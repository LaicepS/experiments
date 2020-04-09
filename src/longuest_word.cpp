#include <algorithm>
#include <iostream>
#include <range/v3/algorithm/any_of.hpp>
#include <range/v3/algorithm/max_element.hpp>
#include <range/v3/view/all.hpp>
#include <string>
#include <string_view>
#include <unordered_set>

#include "dtl.h"

#include "range/v3/algorithm.hpp"
#include "range/v3/range.hpp"
#include "range/v3/view.hpp"

using namespace std;
using namespace dtl;

namespace r = ranges;
namespace rv = ranges::views;
namespace ra = ranges::actions;

using Dict = unordered_set<string>;

bool is_madeup(string_view const & word, string_view const & original_word, Dict const & dict) {
    if(can_find(dict, string(word)) && word != original_word)
	return true;

    auto word_indexes = rv::iota(0u, word.size());
    return r::any_of(word_indexes, [&] (auto const i) {
	auto const & prefix = word.substr(0, i + 1);
	auto const & suffix = word.substr(i + 1);
	return can_find(dict, string(prefix)) && is_madeup(suffix, original_word, dict);
    });
}

bool is_madeup(string_view const & word, Dict const & dict) {
    return is_madeup(word, word, dict);
}

optional<string> longuest_madeup_word(Dict const &dict) {
  auto made_up_words = dict | rv::filter([&](auto const &word) { return is_madeup(word, dict); });

  auto is_less = [](auto const &a, auto const &b) { return a.size() < b.size(); };

  auto longuest = r::max_element(made_up_words, is_less);

  if(longuest == r::end(made_up_words))
      return {};
  else
      return *longuest;
}

int main() {
  {
      auto longuest = longuest_madeup_word( {"cat", "er", "banana", "dog", "nana", "walk", "walker", "dogwalker"});
      assert(longuest.value() == "dogwalker");
  }

  {
      auto longuest = longuest_madeup_word({"cat", "dog"});
      assert(!longuest.has_value());
  }

  {
      auto longuest = longuest_madeup_word({"cat", "dog", "gy", "doggy"});
      assert(longuest.value() == "doggy");
  }

  {
      auto longuest = longuest_madeup_word({"cat", "dog", "doggy"});
      assert(!longuest.has_value());
  }

  return 0;
}
