# Link libraries
target_link_libraries("${CLARICPP}" PRIVATE ${GMP_LIBRARIES})

# Add sub directories
add_subdirectory(utils)
add_subdirectory(expression)
add_subdirectory(simplification)
