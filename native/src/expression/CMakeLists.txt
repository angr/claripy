# Add current directory's source files
target_sources("${SHARED_LIB_NAME}" PRIVATE
	cache_key.cpp
)

# Add subdirectories
add_subdirectory(private)
add_subdirectory(hash)
add_subdirectory(raw)
