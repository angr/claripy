# Add current directory's source files
target_sources("${CLARICPP}" PRIVATE
    c_headers.cpp # Enable use of gcc -E api.h
    annotation.cpp
    create.cpp
    expr.cpp
    backend.cpp
    api.cpp
)
