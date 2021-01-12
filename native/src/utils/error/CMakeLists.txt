# Add current directory's source files
target_sources("${SHARED_LIB_NAME}" PRIVATE
	claricpp.cpp
	unexpected.cpp
	python.cpp
)
