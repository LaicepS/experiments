#include <algorithm>
#include <cassert>
#include <iostream>
#include <unordered_map>
#include <vector>

#include "NamedType/named_type.hpp"
#include "NamedType/underlying_functionalities.hpp"

#include "range/v3/action.hpp"
#include "range/v3/algorithm.hpp"
#include "range/v3/range.hpp"
#include "range/v3/range/conversion.hpp"
#include "range/v3/view.hpp"

using Height = fluent::NamedType<int, struct HeightTag, fluent::Comparable>;
using Weight = fluent::NamedType<int, struct WidthTag, fluent::Comparable>;

struct Member {
  Height height;
  Weight weight;

  bool operator==(Member const& rhs) const {
    return height == rhs.height && weight == rhs.weight;
  }
};

namespace std {
template <>
struct hash<Member> {
  size_t operator()(Member const& m) const {
    return std::hash<int>()(m.weight.get()) ^ std::hash<int>()(m.height.get());
  }
};
}  // namespace std

using namespace std;
namespace rv = ranges::views;
namespace ra = ranges::actions;

using AdjacencyArray = unordered_map<Member, vector<Member>>;
using Graph = AdjacencyArray;

using PathSize = fluent::
    NamedType<int, struct PathSizeT, fluent::Addable, fluent::Comparable>;

bool can_climb(Member const& top, Member const& below) {
  return top.height < below.height && top.weight < below.weight;
}

Graph build_acyclic_graph(vector<Member> const& members) {
  auto build_neighbors = [&](auto const& m) {
    auto climbable = members | rv::filter([&](auto const& other) { return can_climb(m, other); });
    return ranges::to<vector<Member>>(climbable);
  };

  auto node_to_neighbors =
      members | rv::transform([&](auto const& m) { return make_pair(m, build_neighbors(m)); });

  return ranges::to<Graph>(node_to_neighbors);
}

PathSize longuest_path(Graph const& graph,
                       Member const& m,
                       unordered_map<Member, PathSize>& cache) {
  if (cache.find(m) != end(cache))
    return cache.at(m);

  if (graph.at(m).empty())
    return PathSize(1);

  auto const& neighbors = graph.at(m);
  auto neighbor_sizes =
      neighbors | rv::transform([&](auto const& n) { return longuest_path(graph, n, cache); });

  auto const max_path = ranges::max(neighbor_sizes) + PathSize(1);
  cache.insert(make_pair(m, max_path));

  return max_path;
}

PathSize longuest_path(Graph const& graph) {
  PathSize longuest(-1);
  unordered_map<Member, PathSize> members_longuest_path;

  auto all_longuest_path = graph | rv::transform([&](auto const& node) {
                             return longuest_path(graph, node.first, members_longuest_path);
                           });

  return ranges::max(all_longuest_path);
}

int longuest_tower(vector<Member> const& members) {
  if (members.empty())
    return 0;

  auto const& graph = build_acyclic_graph(members);
  return longuest_path(graph).get();
}

int main() {
  assert(0 == longuest_tower({}));
  assert(1 == longuest_tower({{Height(100), Weight(120)}}));

  assert(1 == longuest_tower({{Height(100), Weight(120)},
                              {Height(90), Weight(130)},
                              {Height(110), Weight(115)}}));

  assert(6 == longuest_tower({{Height(65), Weight(100)},
                              {Height(70), Weight(150)},
                              {Height(56), Weight(90)},
                              {Height(75), Weight(190)},
                              {Height(60), Weight(95)},
                              {Height(68), Weight(110)}}));
  return 0;
}
