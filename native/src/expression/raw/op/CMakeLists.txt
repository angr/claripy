# Autogenerate files as needed
message("Autogenerating op class code files...")
execute_process(COMMAND
	python3 ./autogen.py
	WORKING_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}"
	COMMAND_ERROR_IS_FATAL ANY
)

# Add source files
# TODO: make clean
file(READ sources.txt AUTOGEN_SOURCES)
target_sources("${SHARED_LIB_NAME}" PRIVATE
	${AUTOGEN_SOURCES}
	base.cpp
)
