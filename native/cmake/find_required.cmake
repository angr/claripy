# This file defines find_required_program
# This is the same as 3.18+'s find_program(REQUIRED)

macro(find_required_library VARI FIRST)
    find_library("${VARI}" NAMES "${FIRST}" ${ARGN})
    if ("${${VARI}}" STREQUAL "${VARI}-NOTFOUND")
        message(FATAL_ERROR "Could not find library: ${FIRST}" ${ARGN})
    endif()
endmacro()

macro(find_required_program VARI FIRST)
    find_program("${VARI}" NAMES "${FIRST}" ${ARGN})
    if ("${${VARI}}" STREQUAL "${VARI}-NOTFOUND")
        message(FATAL_ERROR "Could not find program: ${FIRST}" ${ARGN})
    endif()
endmacro()
