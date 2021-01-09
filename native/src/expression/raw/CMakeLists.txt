# Add current directory's source files
target_sources("${SHARED_LIB_NAME}" PRIVATE
	symbolic.cpp
	concrete.cpp
	base.cpp
)

# Add type and op sources
add_subdirectory(type)
add_subdirectory(op)
