if(CLANG_TIDY)
	message("Overriding some static analysis checks for testlib")
	set(OVERRIDE_CHECKS
		"-cppcoreguidelines-avoid-magic-numbers"
		"-readability-magic-numbers"
	)
	string(REPLACE ";" "," OVERRIDE_CHECKS "${OVERRIDE_CHECKS}")
	set(OVERRIDE_CHECKS "-checks=${OVERRIDE_CHECKS}")
	list(APPEND CMAKE_CXX_CLANG_TIDY "${OVERRIDE_CHECKS}")
	list(APPEND CMAKE_C_CLANG_TIDY "${OVERRIDE_CHECKS}")
endif()

# Create the test library target that test cases link to
# Then add headers and sources to the test library
add_library("${TESTLIB}" SHARED)
target_link_libraries("${TESTLIB}" PRIVATE "${CLARICPP}")
target_include_directories("${TESTLIB}" PRIVATE "${CLARICPP_SRC}")

# Include additional header files
message(STATUS "Including boost headers for target: ${TESTLIB}")
target_include_directories("${TESTLIB}" SYSTEM PRIVATE ${Boost_INCLUDE_DIRS})

# Add subdirectories
add_subdirectory(testlib)
