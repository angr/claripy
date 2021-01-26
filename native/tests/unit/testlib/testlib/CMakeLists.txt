target_sources("${TESTLIB}" PRIVATE
	test_func.cpp
	factory.cpp
)

# Add subdirectories
add_subdirectory(private)
