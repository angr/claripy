# Add current directory's source files
target_sources("${CLARICPP}" PRIVATE
    ffi.cpp # Enable use of gcc -E api.h
    big_int.cpp
)

# Add sub directories
add_subdirectory(util)
add_subdirectory(expr)
add_subdirectory(simplify)
add_subdirectory(backend)
add_subdirectory(api)

# FFI API source file
# FFI cdefs should be all contained within the intermediate file generated from this
if (CMAKE_CURRENT_SOURCE_DIR MATCHES "/$")
    message(FATAL_ERROR "CMAKE_CURRENT_SOURCE_DIR is weird")
else()
    get_filename_component(SRC_DIR "${CMAKE_CURRENT_SOURCE_DIR}" NAME) # src
    set(CDEFS_SOURCE_F "${SRC_DIR}/ffi.cpp" PARENT_SCOPE)
endif()
