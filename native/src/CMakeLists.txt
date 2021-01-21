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

# Clang is overly cautious and gives warnings that do not apply here
# So for the specific source file, we reduce them back to warnings
if (CMAKE_CXX_COMPILER_ID MATCHES "Clang")
	set(FNAME "${CMAKE_CURRENT_SOURCE_DIR}/expression/raw/op/literal.cpp")
	message(WARNING "Reducing uninitialized errors to warnings for ${FNAME}")
	set_source_files_properties("${FNAME}"
		PROPERTY COMPILE_FLAGS "-Wno-error=uninitialized"
	)
endif()

# Add sub directories
add_subdirectory(utils)
add_subdirectory(expression)
