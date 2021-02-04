target_sources("${TESTLIB}" PRIVATE
	expression_factory.cpp
	test_func.cpp
)

# Add subdirectories
add_subdirectory(private)
