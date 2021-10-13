# Add current directory's source files
target_sources("${CLARICPP}" PRIVATE
    api.cpp
)

# Add sub directories
add_subdirectory(utils)
add_subdirectory(expression)
add_subdirectory(simplification)
