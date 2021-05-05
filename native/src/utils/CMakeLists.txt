# Add current directory's source files
target_sources("${CLARICPP}" PRIVATE
	stack_limit.cpp
)

# Add subdirectories
add_subdirectory(log)
