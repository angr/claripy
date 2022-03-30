# This files defines functions for timestamp checking things

# Return TRUE iff WHAT is at least as old as every item in ITEMS
function(is_eldest WHAT ALL_ITEMS RET_VAR)
    foreach(I IN LISTS ALL_ITEMS)
        if ("${I}" IS_NEWER_THAN "${WHAT}")
            set("${RET_VAR}" FALSE PARENT_SCOPE)
            return()
        endif()
    endforeach()
    set("${RET_VAR}" TRUE PARENT_SCOPE)
    return()
endfunction()

# Return TRUE iff WHAT is at least as old as DIR and every item in DIR recursively
function(is_eldest_of_dir WHAT DIR RET_VAR)
    file(GLOB_RECURSE ALL_ITEMS LIST_DIRECTORIES true "${DIR}/*")
    LIST(PREPEND ALL_ITEMS "${DIR}")
    is_eldest("${WHAT}" "${ALL_ITEMS}" RET)
    set("${RET_VAR}" "${RET}" PARENT_SCOPE)
endfunction()