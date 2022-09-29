# Add current directory's source files
target_sources("${CLARI}" PRIVATE
	recurrence_guard.cpp
	stack_limit.cpp
	terminate.cpp
)

# Add subdirectories
add_subdirectory(err)
add_subdirectory(backtrace)
add_subdirectory(log)
