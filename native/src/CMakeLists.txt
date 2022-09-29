# Add current directory's source files
target_sources("${CLARI}" PRIVATE
    big_int.cpp
)

# Add sub directories
add_subdirectory(util)
add_subdirectory(expr)
add_subdirectory(create)
add_subdirectory(simplify)
add_subdirectory(backend)

# API
if (BUILD_API)
    add_subdirectory(api)
endif()