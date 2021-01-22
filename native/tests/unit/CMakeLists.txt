# Define testlib constants
set(TESTLIB_SRC "${CMAKE_CURRENT_SOURCE_DIR}/testlib")
set(TESTLIB "testlib")

# Create the test library target that test cases link to
# Then add headers and sources to the test library
add_library("${TESTLIB}" SHARED)
target_link_libraries("${TESTLIB}" PRIVATE "${CLARICPP}")
target_include_directories("${TESTLIB}" PRIVATE "${CLARICPP_SRC}")
add_subdirectory("${TESTLIB_SRC}")

# Include additional header files
message(STATUS "Including boost headers for target: ${TESTLIB}")
target_include_directories("${TESTLIB}" SYSTEM PRIVATE ${Boost_INCLUDE_DIRS})

# SimpleTest
set(SIMPLE_TEST_DIR "${CMAKE_CURRENT_SOURCE_DIR}")
include(SimpleTest)

# Add test cases
message(STATUS "Adding unit tests:")
simple_test(simple_test)
add_subdirectory(utils)
add_subdirectory(expression)
