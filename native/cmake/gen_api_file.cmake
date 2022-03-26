# This file defines gen_api_file
include(read_lines)
include (hash_dir)

# Generates API_SOURCE
function(gen_api_file API_TARGET API_SOURCE BINDER_DIR) # Append 'must include' files
    set(MUST_INCLUDE "${ARGN}")

    # Remove bad auto-gen'd code
    if (EXISTS "${BINDER_DIR}/std")
        message(STATUS "Removing undesired auto-generated code...")
        file(REMOVE "${BINDER_DIR}/${API_TARGET}.modules")
        file(REMOVE "${BINDER_DIR}/${API_TARGET}.sources")
        file(REMOVE_RECURSE "${BINDER_DIR}/std") # std bindings
    endif()

    # Hash check BINDER_DIR in case clang-format or something broke it
    # This is useful for developers; ex. detecting if clang-format edited autogen'd code
    hash_dir_store_check("${BINDER_DIR}" "Binder directory is polluted; refusing to proceed.")

    # Determine if cache can be used
    if (EXISTS "${API_SOURCE}")
        set(RET TRUE)
        # Check timestamps of includes
        foreach(INC IN LISTS MUST_INCLUDE)
            if ("${INC}" IS_NEWER_THAN "${API_SOURCE}")
                set(RET FALSE)
                break() # No point in looking more
            endif()
        endforeach()
        #  Bail if cache is fine
        if ("${RET}")
            message(STATUS "Using existing API code")
            return()
        else()
            message("Regenerating API code")
        endif()
    else()
        message("Auto-generating API code")
    endif()

    # Split code into headers and a body
    # Appends to headers, overwrites body as a list
    function(split_code DATA HEADERS_NAME BODY_NAME)
        set(BODY "")
        foreach(LINE IN LISTS DATA)
            if (LINE MATCHES "^#include") # Technically this can fail but probably not
                list(APPEND "${HEADERS_NAME}" "${LINE}")
            else()
                string(REPLACE ";" "\\;" LINE "${LINE}")
                list(APPEND BODY "${LINE}") # Ignores leading new lines
            endif()
        endforeach()
        set("${BODY_NAME}" "${BODY}" PARENT_SCOPE)
        set("${HEADERS_NAME}" "${${HEADERS_NAME}}" PARENT_SCOPE)
    endfunction()

    # Checks
    if (NOT EXISTS "${BINDER_DIR}")
        message(FATAL_ERROR "binder directory does not exist; please run binder first")
    endif()

    # Must includes headers
    set(HEADERS "")
    get_filename_component(API_SOURCE_DIR "${API_SOURCE}" DIRECTORY)
    foreach(INC IN LISTS MUST_INCLUDE)
        file(RELATIVE_PATH INC "${API_SOURCE_DIR}" "${INC}")
        list(APPEND HEADERS "#include \"${INC}\"")
    endforeach()

    # Read in file as list of lines (cannot use file(STRINGS) because semicolons :( )
    message(STATUS "Parsing binder generated code...")
    set(IN_FILE "${BINDER_DIR}/${API_TARGET}.cpp")
    read_lines("${IN_FILE}" RAW_LINES)
    split_code("${RAW_LINES}" HEADERS BODY_LINES)

    # Extract forward decls
    string(FIND "${BODY_LINES}" "PYBIND11_MODULE(" INDEX)
    string(SUBSTRING "${BODY_LINES}" 0 "${INDEX}" DECL_LINES) # Decl
    string(SUBSTRING "${BODY_LINES}" "${INDEX}" -1 BODY_LINES) # Remove decls from BODY_LINES
    set(DECLS "")
    foreach(DECL IN LISTS DECL_LINES) # list(FILTER) cannot handle ';'s
        if (NOT "${DECL}" MATCHES "bind_std") # strip out std stuff
            string(APPEND DECLS "${DECL}\n")
        endif()
    endforeach()
    string(STRIP "${DECLS}" DECLS)

    # Remove closing }
    string(FIND "${BODY_LINES}" "}" INDEX REVERSE)
    string(SUBSTRING "${BODY_LINES}" "${INDEX}" -1 TO_DELETE)
    if (NOT (TO_DELETE STREQUAL "" OR TO_DELETE MATCHES "^}[;\\s]*$")) # Allow ; because this is a list so \n = ;
        message(FATAL_ERROR "${IN_FILE} failed had unexpected code. It ended with: ${TO_DELETE}")
    endif()
    string(SUBSTRING "${BODY_LINES}" 0 "${INDEX}" BODY_LINES)

    # Generate output string
    set(MERGED "namespace API::Binder {\n\n${DECLS}\n\n} // namespace API::Binder\n\n\n")
    foreach(LINE IN LISTS BODY_LINES)
        if (NOT "${LINE}" MATCHES "bind_std") # strip out std stuff; list(FILTER) cannot handle ';'s
            string(REPLACE "ModuleGetter" "API::Binder::ModuleGetter" LINE "${LINE}") # namespace
            string(REPLACE "bind_" "API::Binder::bind_" LINE "${LINE}") # namespace
            string(APPEND MERGED "${LINE}\n")
        endif()
    endforeach()
    string(STRIP "${MERGED}" MERGED)

    # Insert manual invocation
    message(STATUS "Generating main source code...")
    string(APPEND MERGED "\n\n\t// Manual API call\n\tAPI::bind_manual(M);\n}")

    # Add source files
    message(STATUS "Merging auto-generated source files...")
    file(GLOB SOURCES "${BINDER_DIR}/*/*.cpp")
    foreach(NEXT IN LISTS SOURCES)
        read_lines("${NEXT}" DATA)
        split_code("${DATA}" HEADERS BODY_LINES) # Store headers and body
        # Body
        list(JOIN BODY_LINES "\n" BODY)
        string(STRIP "${BODY}" BODY)
        string(REPLACE "void bind_" "namespace API::Binder {\nvoid bind_" BODY "${BODY}") # namespace
        string(REPLACE "PyCallBack_Util_Err_Claricpp, std::exception>" "PyCallBack_Util_Err_Claricpp>" BODY "${BODY}")
        # Add to merged
        file(RELATIVE_PATH FNAME "${API_SOURCE_DIR}" "${NEXT}")
        string(APPEND MERGED "\n\n\n//\n// File: ${FNAME}\n//\n\n\n${BODY}\n} // namespace API::Binder")
    endforeach()

    # Consolidate headers
    list(REMOVE_DUPLICATES HEADERS)
    list(FILTER HEADERS EXCLUDE REGEX "__") # We do not want internal headers (this is probably safe?)

    # Create code
    message(STATUS "Generating final API code...")
    set(WRITE_OUT "// Claricpp API\n\n")
    foreach(INC IN LISTS HEADERS)
        string(APPEND WRITE_OUT "${INC}\n")
    endforeach()
    file(RELATIVE_PATH FNAME "${API_SOURCE_DIR}" "${IN_FILE}")
    string(APPEND WRITE_OUT "\n\n//\n// Derived from file: ${FNAME}\n//\n\n\n${MERGED}")

    # Complete source file
    message(STATUS "Writing out API code to ${API_SOURCE}")
    file(WRITE "${API_SOURCE}" "${WRITE_OUT}") # Write all at once; tight loop append seems buggy
endfunction()
