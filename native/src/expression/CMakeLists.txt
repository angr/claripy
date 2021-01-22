# Add current directory's source files
target_sources("${CLARICPP}" PRIVATE
	cache_key.cpp
)

# Add subdirectories
add_subdirectory(hash)
add_subdirectory(raw)
