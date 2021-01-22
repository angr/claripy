# Add current directory's source files
target_sources("${CLARICPP}" PRIVATE
	recurrence_guard.cpp
)

# Add subdirectories
add_subdirectory(error)
add_subdirectory(log)
