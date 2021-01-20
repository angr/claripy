# Create the shared object target
add_library("${SHARED_LIB_NAME}" SHARED
	# Annotation
	./annotation/base.cpp
	./annotation/simplification_avoidance.cpp
	# Op
	./op/classifications.cpp
	# Simplification
	./simplification/private/op_map.cpp
	./simplification/simplifiers.cpp
	./simplification/simplify.cpp
)

# Add sub directories
add_subdirectory(utils)
add_subdirectory(expression)

# Configure library compilation and linking
if(CMAKE_BUILD_TYPE MATCHES Release)
	set_property(TARGET "${SHARED_LIB_NAME}" PROPERTY INTERPROCEDURAL_OPTIMIZATION TRUE)
endif()
