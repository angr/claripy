# Add current directory's source files
target_sources("${CLARICPP}" PRIVATE
    base.cpp
)

# Add sub directories
add_subdirectory(z3)
