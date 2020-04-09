#pragma once

template<typename Cont, typename V>
bool can_find(Cont const & dict, V const & value) {
    return dict.find(value) != dict.end();
}
