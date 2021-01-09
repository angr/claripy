# Autogenerate files as needed
execute_process(COMMAND
	python3 autogen.py
	WORKING_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}"
)

# Add source files
# TODO: make clean
file(READ sources.txt AUTOGEN_SOURCES)
target_sources("${SHARED_LIB_NAME}" PRIVATE
	${AUTOGEN_SOURCES}
	base.cpp
)
