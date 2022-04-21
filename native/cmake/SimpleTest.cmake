# Define a function which should be used to create every Claricpp unit test
# Requires: SIMPLE_TEST_DIR set to the desired test directory
# Requires: Unit testing be enabled and CTest be included before this
# Also defines a target used to build every unit test

# Error checking
if (NOT DEFINED SIMPLE_TEST_DIR)
	message(FATAL_ERROR "SimpleTest requires the SIMPLE_TEST_DIR variable be defined."
			"This must be defined before including the SimpleTest.cmake file"
	)
endif()

# Inform user about static analysis
if(CLANG_TIDY OR LWYU)
	message("Turning off some static analysis for test cases.")
endif()

# Define an 'all tests' target
set(BUILD_TESTS_TARGET "unit_tests")
add_custom_target("${BUILD_TESTS_TARGET}" ALL COMMENT "Target which depends on all tests")

# Create a function to add test cases
# This file generates a test case from a cpp file: ./<FNAME>.cpp
# <FNAME>.cpp must contain a function named <FNAME> of type int();
# This is the function that will be tested, it's return value will be the test return code
# Additional required cpp files can be passed in as extra arguments
# Test cases must have a local link, src, to /claripy/native/src
function(simple_test FUNC_NAME)

	# Usage check
	if ("${FUNC_NAME}" MATCHES "[/\.]")
		message(FATAL_ERROR
			"simple_test does not allow '.' or '/' in its input."
			"\tIt was given: ${FUNC_NAME}"
		)
	endif()

	# Disable some static analysis for test cases
	# We don't need it on test cases and it causes some issues
	# Note: By default unset only unsets within local scope
	if(LWYU)
		unset(CMAKE_LINK_WHAT_YOU_USE)
		set(LWYU OFF)
	endif()
	if(CLANG_TIDY)
		set(OVERRIDE_CHECKS
			"-readability-convert-member-functions-to-static"
			"-cppcoreguidelines-avoid-magic-numbers"
			"-readability-magic-numbers"
		)
		string(REPLACE ";" "," OVERRIDE_CHECKS "${OVERRIDE_CHECKS}")
		set(OVERRIDE_CHECKS "-checks=${OVERRIDE_CHECKS}")
		list(APPEND CMAKE_CXX_CLANG_TIDY "${OVERRIDE_CHECKS}")
		list(APPEND CMAKE_C_CLANG_TIDY "${OVERRIDE_CHECKS}")
	endif()

	# Determine the test prefix from the path
	string(LENGTH "${SIMPLE_TEST_DIR}/" ST_LEN)
	if(NOT CMAKE_CURRENT_SOURCE_DIR STREQUAL SIMPLE_TEST_DIR)
		string(SUBSTRING "${CMAKE_CURRENT_SOURCE_DIR}" "${ST_LEN}" -1 SUBPATH)
	else()
		set(SUBPATH "")
	endif()
	string(REPLACE "/" "-" TEST_PREFIX "${SUBPATH}")
	string(LENGTH "${TEST_PREFIX}" TEST_PREFIX_LEN)
	if(NOT "${TEST_PREFIX_LEN}" EQUAL 0)
		set(TEST_PREFIX "${TEST_PREFIX}-")
	endif()

	# Create the test binary
	set(TEST_NAME "${TEST_PREFIX}${FUNC_NAME}")
	set(BINARY "${TEST_NAME}.test")
	add_executable("${BINARY}" "${FUNC_NAME}.cpp" ${ARGN})

	## Add and config test
	message(STATUS "\t${TEST_NAME}")
	add_test("${TEST_NAME}" "./${BINARY}")
	add_dependencies("${BUILD_TESTS_TARGET}" "${TEST_NAME}.test")

	# Config test
	target_link_libraries("${BINARY}" PRIVATE "${TESTLIB}")
	target_include_directories("${BINARY}" SYSTEM PRIVATE "${TESTLIB_SRC}/..")
	target_compile_definitions("${BINARY}" PRIVATE "_GLIBCXX_ASSERTIONS")
	target_compile_options("${BINARY}" PRIVATE
		"-fasynchronous-unwind-tables"
		"-grecord-gcc-switches"
		"-O0"
		"-g"
	)
	if(CMAKE_BUILD_TYPE MATCHES Debug)
		target_link_options("${BINARY}" PRIVATE "-rdynamic")  # For debugging
	endif()

	# Add memcheck test
	if(RUN_MEMCHECK_TESTS)
		set(MEMCHECK "${CMAKE_MEMORYCHECK_COMMAND}" "${CMAKE_MEMORYCHECK_COMMAND_OPTIONS}")
		separate_arguments(MEMCHECK)
		add_test("${TEST_NAME}.memcheck" ${MEMCHECK} "./${BINARY}")
	endif()

endfunction()
