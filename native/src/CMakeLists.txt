# Add current directory's source files
target_sources("${CLARICPP}" PRIVATE
    api.cpp
)

# Add sub directories
add_subdirectory(util)
add_subdirectory(expr)
add_subdirectory(simplification)
add_subdirectory(backend)
