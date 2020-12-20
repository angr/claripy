# Enable memory testing for our tests
if(ENABLE_MEMCHECK)
	if("${APPLE}")
		message(WARNING "Valgrind is not supported on newer version of MacOS. Skipping.")
		set(RUN_MEMCHECK_TESTS OFF)
	else()
		find_program(CMAKE_MEMORYCHECK_COMMAND "valgrind" REQUIRED)
		set(CMAKE_MEMORYCHECK_COMMAND_OPTIONS "--trace-children=yes --leak-check=full")
		set(RUN_MEMCHECK_TESTS ON)
	endif()
endif()

# Enable native testing
add_subdirectory(./native)
