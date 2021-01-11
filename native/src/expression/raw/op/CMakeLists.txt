# Autogenerate files as needed
message("Autogenerating op class code files...")
# Older versions of cmake to not support COMMAND_ERROR_IS_FATAL
# so instead we utilize RESULT_VARIABLE (singula)
execute_process(COMMAND
	python3 ./autogen.py
	WORKING_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}"
	RESULT_VARIABLE RET
)
if(NOT RET EQUAL 0)
	message(FATAL_ERROR "Autogen.py failed")
endif()

# Add source files
# TODO: make clean
file(READ sources.txt AUTOGEN_SOURCES)
target_sources("${SHARED_LIB_NAME}" PRIVATE
	${AUTOGEN_SOURCES}
	base.cpp
	if.cpp
)
