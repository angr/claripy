target_sources("${TESTLIB}" PRIVATE
	test_func.cpp
	error.cpp
)

# Add subdirectories
add_subdirectory(private)
