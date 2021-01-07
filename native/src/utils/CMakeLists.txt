# Add current directory's source files
target_sources("${SHARED_LIB_NAME}" PRIVATE
	error/claricpp.cpp
)

# Add log source files
add_subdirectory(log)
