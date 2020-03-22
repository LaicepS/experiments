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

  grid_solver(grid const &g_) {
    to_solver_grid(g_);
    update_all_cands();
  }

  void to_solver_grid(grid const &grid_to_solve) {
    for (int row = 0; row < g.size(); row++)
      for (int col = 0; col < g[0].size(); col++)
        g[row][col].s = grid_to_solve[row][col];
  }

  void update_all_cands() {
    for (int row = 0; row < g.size(); row++)
      for (int col = 0; col < g[row].size(); col++)
        update_cand(row, col);
  }

  void update_cand(int row, int col) {
    auto const cell = g[row][col];
    if (!cell.s)
      return;

    erase_cand(cell.s.value(), row, col);
  }

  void erase_cand(value cell_value, int row, int col) {
    for (int i = 0; i < grid_size; i++)
      if (i != col)
        g[row][i].erase(cell_value);

    for (int i = 0; i < grid_size; i++)
      if (i != row)
        g[i][col].erase(cell_value);
  }

  struct solver_square {

    solver_square() {
      for (int i = 1; i <= grid_size; i++)
        cands.insert(i);
    }

    void erase(value v) {
      cands.erase(v);
      if (cands.size() == 1)
        s = *cands.begin();
    }

    using candidates = unordered_set<value>;

    square s;
    candidates cands;
  };

  using solver_grid = array<array<solver_square, grid_size>, grid_size>;

  grid solve() { return to_grid(); }

  grid to_grid() {
    grid r;
    for (int row = 0; row < g.size(); row++)
      for (int col = 0; col < g[0].size(); col++)
        r[row][col] = g[row][col].s;

    return r;
  }

  solver_grid g;
};

optional<grid> solve(grid const &g) { return grid_solver(g).solve(); }

int main() {
  grid basic_grid = {array<square, grid_size>({1, 2, 3, 4}),
                     array<square, grid_size>({3, 4, 1, 2}),
                     array<square, grid_size>({2, 3, 4, 1}),
                     array<square, grid_size>({4, 1, 2, 3})};

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
