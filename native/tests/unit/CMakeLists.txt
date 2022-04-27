# Config
set(TESTLIB_SRC "${CMAKE_CURRENT_SOURCE_DIR}/testlib")
set(TESTLIB "testlib")

# Create testlib
add_subdirectory("${TESTLIB_SRC}")

# SimpleTest
set(SIMPLE_TEST_DIR "${CMAKE_CURRENT_SOURCE_DIR}")
include(SimpleTest)

# Add test cases
message(STATUS "Adding tests generally in order of dependency.")
message(STATUS "If an early test case fails it will likely take many later ones with it")
message(STATUS "Adding unit tests:")

# Test test system
simple_test(simple_test)
simple_test(sanity_check)

# Add actual test cases
add_subdirectory(util)
add_subdirectory(cuid)
add_subdirectory(hash)
add_subdirectory(factory)
add_subdirectory(expr)
add_subdirectory(op)
add_subdirectory(create)
add_subdirectory(backend)
