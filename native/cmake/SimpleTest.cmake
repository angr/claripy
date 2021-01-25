# Requires: SIMPLE_TEST_DIR set to the desired test directory

# Inform user about static analysis
if(CLANG_TIDY OR LWYU)
	message("Turning off some static analysis for test cases.")
endif()

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
	unset(CMAKE_LINK_WHAT_YOU_USE)
	unset(CMAKE_CXX_CLANG_TIDY)
	unset(CMAKE_C_CLANG_TIDY)

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

	# Configure test case
	set(MAIN_IN  "${SIMPLE_TEST_DIR}/main.cpp.in")
	set(MAIN_OUT "${CMAKE_CURRENT_SOURCE_DIR}/${FUNC_NAME}-testmain.out.cpp")
	configure_file("${MAIN_IN}" "${MAIN_OUT}" @ONLY)

	# Define the binary target and link the headers and shared library
	set(TEST_NAME "${TEST_PREFIX}${FUNC_NAME}")
	set(BINARY "${TEST_NAME}.test")
	add_executable("${BINARY}" "${MAIN_OUT}" "${FUNC_NAME}.cpp" ${ARGN})
	# Link libraries and headers
	target_include_directories("${BINARY}" SYSTEM PRIVATE
		${Boost_INCLUDE_DIRS}
	)
	target_include_directories("${BINARY}" PRIVATE
		"${CLARICPP_SRC}"
		"${TESTLIB_SRC}"
	)
	target_link_libraries("${BINARY}" PRIVATE "${CLARICPP}" "${TESTLIB}")

	## Add the test
	message(STATUS "\t${TEST_NAME}")
	add_test("${TEST_NAME}" "./${BINARY}")

	# Add compile options
	target_compile_definitions("${BINARY}" PRIVATE "_GLIBCXX_ASSERTIONS")
	target_compile_options("${BINARY}" PRIVATE
		"-O0"
		"-g"
		"-fasynchronous-unwind-tables"
		"-grecord-gcc-switches"
	)

	# Add memcheck test
	if(RUN_MEMCHECK_TESTS)
		set(MEMCHECK
			"${CMAKE_MEMORYCHECK_COMMAND}"
			"${CMAKE_MEMORYCHECK_COMMAND_OPTIONS}"
		)
		separate_arguments(MEMCHECK)
		add_test("${TEST_NAME}.memcheck" ${MEMCHECK} "./${BINARY}")
	endif()

	# For make clean
	set_property(TARGET "${BINARY}"
		APPEND PROPERTY ADDITIONAL_CLEAN_FILES
		"${MAIN_OUT}"
	)

endfunction()
