#include <string>
#include <string_view>
#include <unordered_set>

#include "dtl.h"

using namespace std;

using Dict = unordered_set<string>;

bool is_madeup(string_view const & word, string_view const & original_word, Dict const & dict) {
    if(can_find(dict, string(word)) && word != original_word)
	return true;

    for(int i = 0; i < word.size(); i++) {
	auto const & prefix = word.substr(0, i + 1);
	auto const & suffix = word.substr(i + 1);
	if(can_find(dict, string(prefix)) && is_madeup(suffix, original_word, dict))
	    return true;
    }

    return false;
}

bool is_madeup(string_view const & word, Dict const & dict) {
    return is_madeup(word, word, dict);
}

string_view longuest_word(Dict const & dict) {
    string_view longuest_w;
    for(string_view cand: dict) {
	if(is_madeup(cand, dict) && cand.size() > longuest_w.size())
	    longuest_w = cand;
    }
    return longuest_w;
}

int main() {
    return 0;
}
