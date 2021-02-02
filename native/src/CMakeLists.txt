# Create the shared object target
target_sources("${CLARICPP}" PRIVATE
	# Annotation
	./annotation/base.cpp
	./annotation/simplification_avoidance.cpp
	# Op
	# ./op/classifications.cpp
	# Simplification
	# ./simplification/private/op_map.cpp
	# ./simplification/simplifiers.cpp
	# ./simplification/simplify.cpp
)

# Add sub directories
add_subdirectory(soc)
add_subdirectory(utils)
add_subdirectory(expression)
