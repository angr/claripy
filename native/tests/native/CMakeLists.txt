# Create a function to add test cases
# This file generates a test case from a cpp file: ./<FNAME>.cpp
# <FNAME>.cpp must contain a function named <FNAME> of type int();
# This is the function that will be tested, it's return value will be the test return code
# Additional required cpp files can be passed in as extra arguments
function(simple_test FUNC_NAME)

	# Usage check
	if ("${FUNC_NAME}" MATCHES "[/\.]")
		message(FATAL_ERROR
			"simple_test does not allow '.' or '/' in its input."
			"\tIt was given: ${FUNC_NAME}"
		)
	endif()

	# Determine the test prefix from the path
	string(LENGTH "${SIMPLE_TEST_DIR}/" ST_LEN)
	string(SUBSTRING "${CMAKE_CURRENT_SOURCE_DIR}" "${ST_LEN}" -1 SUBPATH)
	string(REPLACE "/" "-" TEST_PREFIX "${SUBPATH}")
	string(LENGTH "${TEST_PREFIX}" TEST_PREFIX_LEN)
	if(NOT "${TEST_PREFIX_LEN}" EQUAL 0)
		set(TEST_PREFIX "${TEST_PREFIX}-")
	endif()

	# Configure test case
	set(MAIN_IN  "${SIMPLE_TEST_DIR}/main.cpp.in")
	set(MAIN_OUT "${CMAKE_CURRENT_SOURCE_DIR}/${FUNC_NAME}-main.cpp")
	list(APPEND ADDITIONAL_CLEAN_FILES "${MAIN_OUT}")
	configure_file("${MAIN_IN}" "${MAIN_OUT}" @ONLY)

	# Generate the and add test
	set(TEST_NAME "${TEST_PREFIX}${FUNC_NAME}")
	set(BINARY "${TEST_NAME}.test")
	add_executable("${BINARY}" "${MAIN_OUT}" "${FUNC_NAME}.cpp" ${ARGN})
	target_link_libraries("${BINARY}" "${SHARED_LIB_NAME}")
	message(STATUS "Adding test case for ${TEST_NAME}")
	add_test("${TEST_NAME}" "./${BINARY}")

	# Add memcheck
	if(RUN_MEMCHECK_TESTS)
		set(MEMCHECK
			"${CMAKE_MEMORYCHECK_COMMAND}"
			"${CMAKE_MEMORYCHECK_COMMAND_OPTIONS}"
		)
		separate_arguments(MEMCHECK)
		add_test("${TEST_NAME}.memcheck" ${MEMCHECK} "./${BINARY}")
	endif()

endfunction()

# Define variables used by simple_test
set(SIMPLE_TEST_DIR "${CMAKE_CURRENT_SOURCE_DIR}")

# Add test cases
add_subdirectory(./ast)
