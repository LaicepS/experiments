#include <stdlib.h>

#define true 1
#define false 0

typedef int value_type;
typedef size_t size_type;
typedef int bool;

/*@
  requires \valid_read(grid+ (0..2));

  assigns \nothing;
  ensures \exists int e; 1 <= e <= 2 && grid[e] != grid[0] ==> \result == 0;
  ensures grid[0] == grid[1] && grid[0] && grid[2] ==> \result == 1;
*/
int all_same(int* grid) {
    if(grid[0] == grid[1] && grid[0] == grid[2])
	return 1;
    else
	return 0;
}

/*@
    predicate
    EqualRanges{A,B}(value_type* a, integer n, value_type* b) =
	\forall integer i; 0 <= i < n ==> \at(a[i], A) == \at(b[i], B);
*/
/*@
    requires \valid_read(a + (0..n-1));
    requires \valid_read(b + (0..n-1));
    assigns \nothing;
    ensures \result <==> EqualRanges{Here,Here}(a, n, b);
*/
bool equal(const value_type* a, size_type n, const value_type* b){
    /*@
      loop invariant 0 <= i <= n;
      loop invariant EqualRanges{Here, Here}(a, i, b);
      loop assigns i;
      loop variant n-i;
      */
    for(size_type i = 0; i < n; i++)
	if (a[i] != b[i])
	    return false;

    return true;
}

/*@
  requires 0 <= n;
  requires \valid_read(a+(0..n-1));
  requires \valid_read(b+(0..n-1));

  assigns \nothing;

  behavior all_equal:
    assumes EqualRanges{Here, Here}(a, n, b);
    ensures \result == n;

  behavior some_different:
    assumes !EqualRanges{Here, Here}(a, n, b);
    ensures 0 <= \result < n;
    ensures EqualRanges{Here, Here}(a, \result, b);
    ensures a[\result] != b[\result];

  complete behaviors;
  disjoint behaviors;
*/
size_type mismatch(const value_type * a, size_type n, const value_type* b) {
    /*@
      loop invariant 0 <= i <= n;
      loop invariant EqualRanges{Here, Here}(a, i, b);
      loop assigns i;
      loop variant n - i;
     */
    for(int i = 0; i < n; i++)
	if (a[i] != b[i])
	    return i;

    return n;
}


int main() {
    return 0;
}
