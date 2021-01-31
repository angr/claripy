# Create the shared object target
target_sources("${CLARICPP}" PRIVATE
	base.cpp
	symbolic.cpp
	concrete.cpp
)
