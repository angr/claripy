# Add current directory's source files
target_sources("${CLARICPP}" PRIVATE
    c_headers.c # Compiled via cc, not cxx
    annotation.cpp
    create.cpp
    expr.cpp
    backend.cpp
    api.cpp
)
