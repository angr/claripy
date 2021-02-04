# Create the shared object target
target_sources("${CLARICPP}" PRIVATE
	# Op
	# ./op/classifications.cpp
	# Simplification
	# ./simplification/private/op_map.cpp
	# ./simplification/simplifiers.cpp
	# ./simplification/simplify.cpp
)

# Link libraries
target_link_libraries("${CLARICPP}" PRIVATE ${GMP_LIBRARIES})

# Add sub directories
add_subdirectory(utils)
