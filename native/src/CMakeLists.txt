# Create the shared object target
target_sources("${CLARICPP}" PRIVATE
	# Op
	# ./op/classifications.cpp
	# Simplification
	# ./simplification/private/op_map.cpp
	# ./simplification/simplifiers.cpp
	# ./simplification/simplify.cpp
)

# Add sub directories
add_subdirectory(utils)
add_subdirectory(expression)
