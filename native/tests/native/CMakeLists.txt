# Create a function to add test cases
# This file generates a test case from a cpp file: ./<FPATH>
# <FPATH> must contain a function with the same name as the filename of type Tests::Native::Test
# This is the function that will be tested, it should return true if the test case passed
# Additional required cpp files can be passed in as extra arguments
function(simple_test TEST_NAME FPATH)
	message(STATUS "Adding test case for ${FPATH}")

	# Configure test case
	set(MAIN_IN  "${CMAKE_CURRENT_SOURCE_DIR}/main.cpp.in")
	set(MAIN_OUT "${CMAKE_CURRENT_SOURCE_DIR}/${TEST_NAME}-main.cpp")
	get_filename_component(FNAME "${FPATH}" NAME_WE)
	configure_file("${MAIN_IN}" "${MAIN_OUT}" @ONLY)

	# Generate the and add test
	set(BINARY "${TEST_NAME}.test")
	add_executable("${BINARY}" "${MAIN_OUT}" "${FPATH}" ${ARGN})
	target_link_libraries("${BINARY}" "${SHARED_LIB_NAME}")
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


# Test cases
simple_test("ast-dummy" "./ast/dummy.cpp")
