#pragma once

#include <algorithm>

namespace dtl {

template<typename cont_type, typename V>
bool can_find(cont_type const & dict, V const & value) {
    return dict.find(value) != dict.end();
}

template<typename cont_type, typename pred_fn>
auto any_of(cont_type const & c, pred_fn fn) {
    return std::any_of(begin(c), end(c), fn);
}
