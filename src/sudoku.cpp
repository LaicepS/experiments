#include <array>
#include <boost/type_traits/declval.hpp>
#include <cassert>
#include <experimental/optional>
#include <iostream>
#include <unordered_set>

#include <boost/variant.hpp>
#include <boost/variant/variant.hpp>

using namespace std;
using namespace std::experimental;

using value = int;

using square = optional<value>;

constexpr auto grid_size = 4;
using grid = array<array<square, grid_size>, grid_size>;

struct grid_solver {

  grid_solver(grid const &g_) : solvable(true) {
    to_solver_grid(g_);
    solvable &= update_all_cands();
  }

  void to_solver_grid(grid const &grid_to_solve) {
    for (int row = 0; row < g.size(); row++)
      for (int col = 0; col < g[0].size(); col++)
        g[row][col].s = grid_to_solve[row][col];
  }

  bool update_all_cands() {
    bool possible = true;
    for (int row = 0; row < g.size(); row++)
      for (int col = 0; col < g[row].size(); col++)
        possible &= update_cand(row, col);

    return possible;
  }

  bool update_cand(int row, int col) {
    auto const cell = g[row][col];
    if (!cell.s)
      return true;

    return erase_cand(cell.s.value(), row, col);
  }

  bool erase_cand(value cell_value, int row, int col) {
    bool possible = true;

    for (int i = 0; i < grid_size; i++)
      if (i != col)
        possible &= g[row][i].erase(cell_value);

    for (int i = 0; i < grid_size; i++)
      if (i != row)
        possible &= g[i][col].erase(cell_value);

    return possible;
  }

  struct solver_square {

    solver_square() {
      for (int i = 1; i <= grid_size; i++)
        cands.insert(i);
    }

    bool erase(value v) {
      cands.erase(v);
      if (cands.size() == 1) {
        s = *cands.begin();
        return true;
      } else if (cands.size() == 0) {
        return false;
      }

      return true;
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
    auto const solve_try = solve(basic_grid);
    assert(solve_try);
    auto const solved = solve_try.value();
    assert(solved[0][0] == 1);
    assert(solved[3][2] == 2);
  }

  {
    auto missing_one_cell = basic_grid;
    missing_one_cell[1][1] = {};

    auto const solve_try = solve(missing_one_cell);
    assert(solve_try);
    auto const solved = solve_try.value();
    assert(solved[1][1] == 4);
  }

  {
    auto missing_two_cells = basic_grid;
    missing_two_cells[0][0] = {};
    missing_two_cells[0][1] = {};
    missing_two_cells[1][0] = {};
    missing_two_cells[1][1] = {};

    print(missing_two_cells);

    auto const solve_try = solve(missing_two_cells);
    assert(solve_try);
    auto const solved = solve_try.value();
    assert(solved == basic_grid);
    print(solved);
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

    print(two_row_missing);
    auto const solve_try = solve(two_row_missing);
    assert(solve_try);
    auto const solved = solve_try.value();
    print(solved);
    assert(solved == basic_grid);
  }

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
