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

/*@
  predicate
    HasValue{A}(value_type* a, size_type n, value_type value) =
      \exists integer i; 0 <= i < n && a[i] == value;
 */
/*@
  requires 0 <= n;
  requires \valid_read(a+(0..n-1));

  assigns \nothing;

  behavior in_array:
    assumes HasValue(a, n, val);
    ensures 0 <= \result < n;
    ensures a[\result] == val;
    ensures !HasValue(a, \result, val);

  behavior not_in_array:
    assumes !HasValue(a, n, val);
    ensures \result == n;

  complete behaviors;
  disjoint behaviors;
*/
size_type find(const value_type* a, size_t n, value_type val) {
    /*@
      loop invariant 0 <= i <= n;
      loop invariant !HasValue(a, i, val);
      loop assigns i;
      loop variant n - i;
    */
    for(size_t i = 0; i < n; i++) {
	if (a[i] == val)
	    return i;
    }

    return n;
}

/*@
  predicate AShareOneValueWithB{A}(value_type* a, size_type m, value_type* b, size_type n) =
    \exists integer i; 0 <= i < m && HasValue(b, n, a[i]);
*/
/*@
  requires \valid_read(a+(0..m-1));
  requires \valid_read(b+(0..n-1));

  assigns \nothing;

  behavior share_one:
    assumes AShareOneValueWithB(a, m, b, n);

    ensures !AShareOneValueWithB(a, \result, b, n);
    ensures HasValue(b, n, a[\result]);
    ensures 0 <= \result < m;

  behavior share_none:
    assumes !AShareOneValueWithB(a, m, b, n);
    ensures \result == m;


  complete behaviors;
  disjoint behaviors;
*/
size_type find_first_of(const value_type* a, size_type m, const value_type* b, size_type n) {
    /*@
      loop invariant 0 <= i <= m;
      loop invariant !AShareOneValueWithB(a, i, b, n);
      loop assigns i;
      loop variant m - i;
    */
    for(size_type i = 0; i < m; i++)
	if (find(b, n, a[i]) != n)
	    return i;

    return m;
}

/*@
  predicate HasAdjacent(value_type* a, integer n) =
    \exists integer i; 0 <= i < n - 1 && a[i] == a[i+1];
*/
/*@
  requires \valid_read(a+(0..n-1));
  assigns \nothing;

  behavior adjacent_exist:
    assumes HasAdjacent(a, n);

    ensures !HasAdjacent(a, \result);
    ensures 0 <= \result < n - 1;
    ensures a[\result] == a[\result+1];

  behavior no_adjacent:
    assumes !HasAdjacent(a, n);
    ensures \result == n;

  complete behaviors;
  disjoint behaviors;
*/
size_type adjacent_find(const value_type* a, size_type n) {
    if (n == 0)
	return n;
    /*@
      loop invariant 0 <= i <= n - 1;
      loop invariant !HasAdjacent(a, i+1);
      loop assigns i;
      loop variant n - i;
    */
    for(size_type i = 0; i < n - 1; i++)
	if(a[i] == a[i+1])
	    return i;

    return n;
}

/*@
  predicate HasSubarray{Here}(value_type * a, integer n, value_type * b, size_type m) =
    \exists integer i; 0 <= i <= n - m && EqualRanges{Here, Here}(a + i, m, b);
*/
/*@
  requires \valid_read(a + (0..n));
  requires \valid_read(b + (0..m));

  ensures m > n ==> \result == m;

  assigns \nothing;

  behavior contains:
    assumes HasSubarray(a, n, b, m);

    ensures \forall integer i; 0 <= i < \result ==> !HasSubarray(a, i + m, b, m);
    ensures EqualRanges{Here, Here}(a + \result, m, b);

  behavior no_subarray:
    assumes !HasSubarray(a, n, b, m);
    ensures \result == m;

  complete behaviors;
  disjoint behaviors;
*/
size_type search(const value_type * a, size_type n, const value_type * b, size_type m) {
    if (m > n)
	return m;

    /*@
      loop invariant 0 <= i <= n - m + 1;
      loop invariant \forall integer j; 0 <= j < i ==> !EqualRanges{Here, Here}(a + j, m, b);
      loop assigns i;
      loop variant n - i;
    */
    for(size_type i = 0; i <= n - m; i++)
	if(equal(a + i, m, b))
	    return i;

    return m;
}


/*@
  axiomatic CountAxiomatic
  {
    logic integer Count{L}(value_type* a, integer n, value_type v)
	reads a[0..n-1];

    axiom CountEmpty:
	\forall value_type *a, v, integer n;
	  n <= 0 ==> Count(a, n, v) == 0;

    axiom CountOneHit:
	\forall value_type *a, v, integer n;
	  a[n] == v ==> Count(a, n + 1, v) == Count(a, n, v) + 1;

    axiom CountOneMiss:
	\forall value_type *a, v, integer n;
	  a[n] != v ==> Count(a, n + 1, v) == Count(a, n, v);

    axiom CountRead{L1,L2}:
	\forall value_type *a, v, integer n;
	  Unchanged{L1,L2}(a, n) ==>
	    Count{L1}(a, n, v) == Count{L2}(a, n, v);
  }
*/
/*@
  lemma CountOne:
    \forall value_type *a, v, integer n;
      Count(a, n + 1, v) == Count(a, n, v) + Count(a + n, 1, v);

  lemma CountUnion:
    \forall value_type *a, v, integer n, k;
	0 <= k ==> Count(a, n + k, v) == Count(a, n, v) + Count(a + n, k, v);

  lemma CountBounds:
    \forall value_type *a, v, integer n;
      0 <= n ==> 0 <= Count(a, n, v) <= n;

  lemma CountMonotonic:
    \forall value_type *a, v, integer m, n;
	0 <= m <= n ==> Count(a, m, v) <= Count(a, n, v);
*/
/*@
  requires \valid_read(a + (0..n-1));

  assigns \nothing;

  ensures \result == Count(a, n, val);
*/

size_type count(const value_type* a, size_type n, value_type val) {
    size_type count = 0;
    /*@
      loop invariant i <= 0 <= n;
      loop invariant count == Count(a, i, val);
      loop assigns i, count;
      loop variant n - i;
    */
    for(size_type i = 0; i < n; i++)
	if(a[i] == val)
	    count++;

    return count;
}

int main() {
    return 0;
}
