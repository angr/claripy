find_package(Doxygen REQUIRED dot)

# Config
include(default)
if (CMAKE_CXX_EXTENSIONS)
	set(CXX_LIB "gnu")
else()
	set(CXX_LIB "c")
endif()
set(PROJECT_LOGO "${CMAKE_CURRENT_SOURCE_DIR}/logo.png")
set(DOXYGEN_IN "${CMAKE_CURRENT_SOURCE_DIR}/Doxyfile.in")
set(DOXYGEN_OUT "${CMAKE_CURRENT_SOURCE_DIR}/Doxyfile")
default(DOXYGEN_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/docs")

# Determine doc sources
set(DOC_SOURCES "src/")
if (BUILD_API)
	string(APPEND DOC_SOURCES " api/")
endif()
if (ENABLE_TESTING)
	string(APPEND DOC_SOURCES " tests/")
endif()

# Copy DOXYGEN_IN -> DOXYGEN_OUT but replace all strings in DOXYGEN_IN
# surrounded with @ signs with the values of the variables they name
# For example: @PROJECT_LOGO@ is replaced with the value of PROJECT_LOGO
message(STATUS "Using Doxyfile template: ${DOXYGEN_IN} to generate: ${DOXYGEN_OUT}")
configure_file("${DOXYGEN_IN}" "${DOXYGEN_OUT}" "@ONLY")

# Create a make target to generate documentation
message(STATUS "Adding doxygen target: ${DOC_MAKE_TARGET}")
add_custom_target("${DOC_MAKE_TARGET}"
	COMMAND "${DOXYGEN_EXECUTABLE}" "${DOXYGEN_OUT}"
	WORKING_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}"
	COMMENT "Generating documentation via Doxygen"
	VERBATIM
)

# For make clean
set_property(TARGET "${DOC_MAKE_TARGET}"
	APPEND PROPERTY ADDITIONAL_CLEAN_FILES
	"${DOXYGEN_OUTPUT_DIRECTORY}"
	"${DOXYGEN_OUT}"
)