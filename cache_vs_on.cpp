#include <cassert>
#include <chrono>
#include <iostream>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

using namespace std;

using pairs = vector<pair<size_t, size_t>>;

pairs pairsWithSum_cache(int sum, vector<int> const &elts) {
  if (elts.size() < 2)
    return {};

  pairs result;
  for (int i = 0; i < elts.size() - 1; i++) {
    for (int j = i + 1; j < elts.size(); j++) {
      if (elts[i] + elts[j] == sum)
        result.push_back(make_pair(i, j));
    }
  }
  return result;
}

pairs pairsWithSum_memory(int sum, vector<int> const &elts) {
  unordered_map<int, vector<size_t>> elts_indexes;
  for (size_t i = 0; i < elts.size(); i++) {
    elts_indexes[elts[i]].push_back(i);
  }

  pairs result;
  for (int i = 0; i < elts.size(); i++) {
    auto const complement = sum - elts[i];
    auto const indexes = elts_indexes.find(complement);
    if (indexes != elts_indexes.end()) {
      for (int j = 0; j < indexes->second.size(); j++) {
        if (i < indexes->second[j])
          result.push_back(make_pair(i, size_t(indexes->second[j])));
      }
    }
  }

  return result;
};

void tests() {
  auto const expected = pairs{{0, 1}};
  auto const expected2 = pairs{{1, 6}, {2, 5}, {7, 8}};

  for (auto f : {pairsWithSum_memory, pairsWithSum_cache}) {
    assert(f(10, {}) == pairs{});
    assert(f(10, {3, 7}) == expected);
    assert(f(10, {5}) == pairs{});
    assert(f(10, {5, 5}) == expected);
    assert(f(10, {0, 8}) == pairs{});
    assert(f(10, {3, 5, 6, 8, 11, 4, 5, -10, 20}) == expected2);
  }
}

int main() {

  tests();

  srand(0);

  vector<int> sizes;
  for (int i = 10; i < 30; i++)
    sizes.push_back(i * 10);

  for (auto size : sizes) {
    vector<int> rand_numbers;
    for (int i = 0; i < size; i++)
      rand_numbers.push_back(rand() % size);

    cout << "With size: " << size << endl;
    for (auto f : {pairsWithSum_cache, pairsWithSum_memory}) {
      auto start = std::chrono::steady_clock::now();

      for (int i = 0; i < 10'000; i++)
        f(size, rand_numbers);

      auto end = std::chrono::steady_clock::now();

      std::cout
          << "\tElapsed: "
          << chrono::duration_cast<chrono::milliseconds>(end - start).count()
          << "ms" << endl;
    }
  }

  return 0;
}
