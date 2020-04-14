#include <algorithm>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <random>
#include <utility>

using namespace std;

pair<int, int> pick_two(int n) {
    auto first  = (rand() % n) + 1;
    int second;
    do {
	second = (rand() % n) + 1;
    } while(second == first);

    if (first < second)
	return make_pair(first, second);
    else
	return make_pair(second, first);
}

vector<int> make_iota_except(int n, pair<int, int> const & exceptions) {
    vector<int> result;
    for(int i = 1; i <= n; i++) {
	if(i != exceptions.first && i != exceptions.second)
	    result.push_back(i);
    }

    return result;
}

int partition(vector<int> & elts, int pivot_idx) {

    auto pivot = elts[pivot_idx];
    swap(elts[0], elts[pivot_idx]);

    int l = 1;
    int r = elts.size() - 1;
    while(l <= r) {
	if (elts[l] > pivot) {
	    swap(elts[l], elts[r]);
	    r--;
	} else if (elts[r] <= pivot) {
	    swap(elts[r], elts[l]);
	    l++;
	} else {
	    r--;
	    l++;
	}
    }

    swap(elts[0], elts[l-1]);
    return l-1;
}

pair<int, int> missing_two(vector<int> & all_but_two) {
    auto const n = all_but_two.size() + 2;
    auto const expected_sum = n*(n+1)/2;
    auto const actual_sum = accumulate(begin(all_but_two), end(all_but_two), 0);
    auto const a_plus_b  = expected_sum - actual_sum;
    auto const pivot = a_plus_b/2;
    auto const pivot_idx = find(begin(all_but_two), end(all_but_two), pivot) - begin(all_but_two);

    if (pivot_idx == all_but_two.size())
	return {pivot, pivot+1};

    auto const new_pivot_idx = partition(all_but_two, pivot_idx);
    auto const expected_sum_till_pivot = pivot*(pivot+1)/2;
    auto const actual_sum_till_pivot = accumulate(begin(all_but_two), begin(all_but_two) + new_pivot_idx + 1, 0);
    auto const a = expected_sum_till_pivot - actual_sum_till_pivot;
    auto const b = a_plus_b - a;

    return {a, b};
}

int main()
{
    for(int n = 2; n < 50; n++) {
	for(int seed = 0; seed < 10; seed++) {
	    std::srand(seed);
	    std::random_device rd;
	    std::mt19937 g(rd());

	    auto random_pair = pick_two(n);
	    auto all_but_two = make_iota_except(n, random_pair);

	    shuffle(begin(all_but_two), end(all_but_two), g);

	    assert(random_pair == missing_two(all_but_two));
	}

    }

    return 0;
}
