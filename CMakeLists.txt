cmake_minimum_required(VERSION 3.7)

set(CPP_WARNINGS " \
    -Wall \
    -Wextra \
    -Wunused \
    -Wshadow \
    -Wnon-virtual-dtor \
    -pedantic \
")

set(CMAKE_CXX_FLAGS "-Werror ${CPP_WARNINGS} ${CMAKE_CXX_FLAGS}")

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

include_directories(.)
include_directories(range-v3/include)

add_executable(circus src/circus.cpp)
add_executable(kth_multiple src/kth_multiple.cpp)
