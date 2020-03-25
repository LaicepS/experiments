#include <array>
#include <boost/type_traits/declval.hpp>
#include <cassert>
#include <experimental/optional>
#include <iostream>
#include <unordered_set>
#include <vector>

#include <boost/variant.hpp>
#include <boost/variant/variant.hpp>

enum erase_result { IMPOSSIBLE, NEW_VALUE, NOTHING };

using namespace std;
using namespace std::experimental;

using value = int;

using square = optional<value>;

constexpr auto grid_size = 4;
using grid = array<array<square, grid_size>, grid_size>;

struct grid_solver {

  using new_numbers = vector<pair<int, int>>;

  grid_solver(grid const &g_) : solvable(true) {
    to_solver_grid(g_);

    while (true) {
      auto const new_numbers = update_all_cands();
      if (!new_numbers) {
        solvable = false;
        return;
      } else {
        if (!new_numbers.value().empty()) {
          cout << "new numbers: " << endl;
          for (auto n : new_numbers.value())
            cout << "new row,col : " << n.first << ", " << n.second << endl;
        }
        if (new_numbers.value().empty())
          return;
      }
    }
  }

  void to_solver_grid(grid const &grid_to_solve) {
    for (int row = 0; row < g.size(); row++)
      for (int col = 0; col < g[0].size(); col++)
        g[row][col].s = grid_to_solve[row][col];
  }

  optional<new_numbers> update_all_cands() {

    new_numbers result;
    for (int row = 0; row < g.size(); row++) {
      for (int col = 0; col < g[row].size(); col++) {
        auto const r = update_cand(row, col);
        if (!r)
          return {};
        auto const new_values = r.value();
        result.insert(end(result), begin(new_values), end(new_values));
      }
    }

    return result;
  }

  optional<new_numbers> update_cand(int row, int col) {
    auto const cell = g[row][col];
    if (!cell.s)
      return new_numbers();

    return erase_cand(cell.s.value(), row, col);
  }

  optional<new_numbers> erase_cand(value cell_value, int row, int col) {
    new_numbers new_values;
    for (int i = 0; i < grid_size; i++) {
      if (i != col) {
        auto res = g[row][i].erase(cell_value);
        switch (res) {
        case IMPOSSIBLE:
          return {};
        case NEW_VALUE:
          new_values.push_back(make_pair(row, i));
          break;
        case NOTHING:
          break;
        }
      }
    }

    for (int i = 0; i < grid_size; i++) {
      if (i != row) {
        auto res = g[i][col].erase(cell_value);
        switch (res) {
        case IMPOSSIBLE:
          return {};
        case NEW_VALUE:
          new_values.push_back(make_pair(i, col));
          break;
        case NOTHING:
          break;
        }
      }
    }

    return new_values;
  }

  struct solver_square {

    solver_square() {
      for (int i = 1; i <= grid_size; i++)
        cands.insert(i);
    }

    erase_result erase(value v) {
      cands.erase(v);
      if (cands.size() == 1)
        return update_with_last_possiblity();
      else if (cands.size() == 0)
        return IMPOSSIBLE;
      else
        return NOTHING;
    }

    erase_result update_with_last_possiblity() {
      auto const last_possibility = *cands.begin();
      if (s) {
        if (s.value() != last_possibility)
          return IMPOSSIBLE;
        else
          return NOTHING;
      } else {
        s = last_possibility;
        return NEW_VALUE;
      }
    }

    using candidates = unordered_set<value>;

    square s;
    candidates cands;
  };

  using solver_grid = array<array<solver_square, grid_size>, grid_size>;

  optional<grid> solve() { return solvable ? to_grid() : optional<grid>(); }

  grid to_grid() {
  grid r;
  for (int row = 0; row < g.size(); row++)
    for (int col = 0; col < g[0].size(); col++)
      r[row][col] = g[row][col].s;

  return r;
}

  solver_grid g;
  bool solvable;
};

optional<grid> solve(grid const &g) { return grid_solver(g).solve(); }

void print(grid const &g) {
  for (int row = 0; row < g.size(); row++) {
    cout << "| ";
    for (int col = 0; col < g[row].size(); col++) {
      auto const rep = g[row][col] ? to_string(g[row][col].value()) : " ";
      cout << rep << " ";
    }
    cout << "|" << endl;
  }
  cout << endl;
}

int main() {
  grid basic_grid = {array<square, grid_size>({1, 2, 3, 4}),
                     array<square, grid_size>({3, 4, 1, 2}),
                     array<square, grid_size>({2, 3, 4, 1}),
                     array<square, grid_size>({4, 1, 2, 3})};
  print(basic_grid);

  {
    grid_solver::solver_square s;
    auto const r = s.erase(3);
    assert(r == NOTHING);
  }

  {
    grid_solver::solver_square s;
    for (int i = 1; i < grid_size - 1; i++) {
      auto const r = s.erase(i);
      assert(r == NOTHING);
    }

    auto const r = s.erase(grid_size);
    assert(r == NEW_VALUE);
    assert(s.s.value() == grid_size - 1);

    auto const redundant_erase = s.erase(1);
    assert(redundant_erase == NOTHING);

    auto const impossible_erase = s.erase(grid_size - 1);
    assert(impossible_erase == IMPOSSIBLE);
  }

  {
    auto const solve_try = solve(basic_grid);
    assert(solve_try);
    auto const solved = solve_try.value();
    assert(solved == basic_grid);
  }

  {
    auto missing_one_cell = basic_grid;
    missing_one_cell[1][1] = {};

    auto const solve_try = solve(missing_one_cell);
    assert(solve_try);
    auto const solved = solve_try.value();
    assert(solved == basic_grid);
  }

  {
    auto missing_top_left = basic_grid;
    missing_top_left[0][0] = {};
    missing_top_left[0][1] = {};
    missing_top_left[1][0] = {};
    missing_top_left[1][1] = {};

    auto const solve_try = solve(missing_top_left);
    assert(solve_try);
    auto const solved = solve_try.value();
    assert(solved == basic_grid);
  }

  {
    auto invalid_grid = basic_grid;
    invalid_grid[0][0] = 2;
    assert(!solve(invalid_grid));
  }

  {
    auto two_row_missing = basic_grid;
    for (int row = 0; row < 2; row++)
      for (int col = 0; col < grid_size; col++)
        two_row_missing[row][col] = {};

    auto hard_grid = two_row_missing;
    hard_grid[1][1] = 4;
    hard_grid[0][2] = 3;
    auto const solve_try = solve(hard_grid);
    assert(solve_try);
    auto const solved = solve_try.value();
    assert(solved == basic_grid);
  }

  /*
  {
    auto two_row_missing = basic_grid;
    for (int row = 0; row < 2; row++)
      for (int col = 0; col < grid_size; col++)
        two_row_missing[row][col] = {};

    print(two_row_missing);
    auto const solve_try = solve(two_row_missing);
    assert(solve_try);
    auto const solved = solve_try.value();
    print(solved);
    assert(solved == basic_grid);
  }
  */

  /*
  {
    auto const solve_try = solve({});
    assert(solve_try);

    auto const empty_solved = solve_try.value();
    assert(empty_solved[0][0]);
  }
  */
  return 0;
}
