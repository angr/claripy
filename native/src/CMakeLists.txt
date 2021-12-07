# Add current directory's source files
target_sources("${CLARICPP}" PRIVATE
    ffi.cpp # Enable use of gcc -E api.h
)

# Add sub directories
add_subdirectory(util)
add_subdirectory(expr)
add_subdirectory(simplification)
add_subdirectory(backend)
add_subdirectory(api)
