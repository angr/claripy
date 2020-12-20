# Use boost
find_package(Boost 1.71 REQUIRED COMPONENTS unit_test_framework)
include_directories("${Boost_INCLUDE_DIRS}")


# Create a function to add test cases
function(boost_test TNAME)
	message(STATUS "Adding test cases for ${TNAME} with files ${ARGN}")

	# Generate test and add it
	add_executable("${TNAME}.test" ${ARGN})
	target_link_libraries("${TNAME}.test"
		"${SHARED_LIB_NAME}"
		Boost::unit_test_framework
	)
	add_test("${TNAME}" "./${TNAME}.test")

	# Add memcheck
	if(RUN_MEMCHECK_TESTS)
		set(MEMCHECK
			"${CMAKE_MEMORYCHECK_COMMAND}"
			"${CMAKE_MEMORYCHECK_COMMAND_OPTIONS}"
		)
		separate_arguments(MEMCHECK)
		add_test("${TNAME}-memcheck" ${MEMCHECK} "./${TNAME}.test")
	endif()

endfunction()


# Test modules
boost_test("ast" "ast.cpp")
