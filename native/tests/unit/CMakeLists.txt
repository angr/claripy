# Define testlib constants
set(TESTLIB_SRC "${CMAKE_CURRENT_SOURCE_DIR}/testlib")
set(TESTLIB "testlib")

# Create testlib
add_subdirectory("${TESTLIB_SRC}")

# SimpleTest
set(SIMPLE_TEST_DIR "${CMAKE_CURRENT_SOURCE_DIR}")
include(SimpleTest)

# Add test cases
message(STATUS "Adding unit tests:")
simple_test(simple_test)
add_subdirectory(utils)
add_subdirectory(expression)
