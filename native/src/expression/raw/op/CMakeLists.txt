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

# Load autogen'd source paths
set(SOURCES_TXT "${CMAKE_CURRENT_SOURCE_DIR}/sources.txt")
file(READ "${SOURCES_TXT}" AUTOGEN_SOURCES)
list(TRANSFORM AUTOGEN_SOURCES PREPEND "${CMAKE_CURRENT_SOURCE_DIR}/")

# Add source files
target_sources("${SHARED_LIB_NAME}" PRIVATE
	${AUTOGEN_SOURCES}
	base.cpp
	if.cpp
)

# For make clean

set_property(DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}"
	APPEND
	PROPERTY ADDITIONAL_CLEAN_FILES
	${AUTOGEN_SOURCES}
	"${CMAKE_CURRENT_SOURCE_DIR}/autogen.hpp"
	"${SOURCES_TXT}"
)
