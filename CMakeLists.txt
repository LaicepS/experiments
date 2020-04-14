cmake_minimum_required(VERSION 3.7)

set(CPP_WARNINGS " \
    -Wall \
    -Wextra \
    -Wunused \
    -Wshadow \
    -Wnon-virtual-dtor \
    -pedantic \
")

set(IGNORED_WARNINGS " \
  -Wno-sign-compare \
")

set(CMAKE_CXX_COMPILER clang++)

set(YCM_FLAGS "-isystem /usr/lib/llvm-9/bin/../include/c++/v1")

set(CMAKE_CXX_FLAGS "-std=c++17 -stdlib=libc++ -Werror ${CPP_WARNINGS} ${IGNORED_WARNINGS} ${YCM_FLAGS} ${CMAKE_CXX_FLAGS}")

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

include_directories(.)
include_directories(range-v3/include)

add_executable(circus src/circus.cpp)
add_executable(kth_multiple src/kth_multiple.cpp)

add_executable(em src/emsdk.cpp)
target_link_libraries(em SDL2)

add_executable(word_distance src/word_distance.cpp)

# find_package( CGAL QUIET COMPONENTS  )
# include( ${CGAL_USE_FILE} )
# find_package( Boost REQUIRED )


# set_source_files_properties(src/cgal.cpp PROPERTIES COMPILE_OPTIONS -fno-rounding-math)

# add_executable(cgal src/cgal.cpp)

# add_to_cached_list( CGAL_EXECUTABLE_TARGETS cgal )
# target_link_libraries(cgal   ${CGAL_LIBRARIES} ${CGAL_3RD_PARTY_LIBRARIES} )

add_executable(respace src/respace.cpp)

add_executable(sudoku src/sudoku.cpp)

add_executable(longuest_word src/longuest_word.cpp)

add_executable(two_missing src/two_missing.cpp)
