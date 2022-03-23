# This file defines functions used for hashing a directory and detecting changes within it
cmake_minimum_required(VERSION 3.17) # ZIP_LISTS

# Config
set(HASHES_FNAME "_hashes.txt")
set(FILES_FNAME "_files.txt")


function(hash_dir_sanity_check FILES HASHES)
    list(LENGTH FILES F_LEN)
    list(LENGTH HASHES H_LEN)
    if (NOT F_LEN EQUAL H_LEN)
        message(FATAL_ERROR "hash_dir sanity check failed: ${F_LEN} != ${H_LEN}")
    endif()
endfunction()

function(hash_dir_get ROOT IGNORE FILES_NAME HASHES_NAME)
    # List items
    string(APPEND ROOT "/")
    file(GLOB_RECURSE FILES
        FOLLOW_SYMLINKS
        LIST_DIRECTORIES true
        RELATIVE "${ROOT}"
        "${ROOT}*"
    )
    list(SORT FILES COMPARE NATURAL) # Do not depend on GLOB to be consistent with order just in case
    # Ignore certain items
    foreach(F IN LISTS IGNORE)
        list(FILTER FILES EXCLUDE REGEX "^${F}$")
    endforeach()
    # Calculate hashes
    set(HASHES "")
    foreach(FS IN LISTS FILES) # Note: directory hash to md5("")
        file(MD5 "${ROOT}${FS}" NEXT_HASH)
        list(APPEND HASHES "${NEXT_HASH}")
    endforeach()
    # Return
    hash_dir_sanity_check("${FILES}" "${HASHES}")
    set("${FILES_NAME}" "${FILES}" PARENT_SCOPE)
    set("${HASHES_NAME}" "${HASHES}" PARENT_SCOPE)
endfunction()

function(hash_dir_store ROOT)
    set(FH "${ROOT}/${HASHES_FNAME}")
    set(FF "${ROOT}/${FILES_FNAME}")
    file(REMOVE "${FH}" "${FF}") # Remove together before writing
    hash_dir_get("${ROOT}" "" FILES HASHES)
    message(STATUS "Writing out ${FF} and ${FH}")
    file(WRITE "${FH}" "${HASHES}")
    file(WRITE "${FF}" "${FILES}")
endfunction()

function(hash_dir_check ROOT ERR_MSG) # Error if different
    file(READ "${ROOT}/${HASHES_FNAME}" OLD_HASHES)
    file(READ "${ROOT}/${FILES_FNAME}" OLD_FILES)
    hash_dir_sanity_check("${OLD_FILES}" "${OLD_HASHES}")
    hash_dir_get("${ROOT}" "${HASHES_FNAME};${FILES_FNAME}" NEW_FILES NEW_HASHES)
    # File list checks
    list(LENGTH OLD_FILES OLD_LEN)
    list(LENGTH NEW_FILES NEW_LEN)
    if (NOT OLD_LEN EQUAL NEW_LEN)
        message(FATAL_ERROR "File lists differ in length.\n${ERR_MSG}")
    elseif(NOT OLD_FILES STREQUAL NEW_FILES)
        message(FATAL_ERROR "File lists differ but same length.\n${ERR_MSG}")
    endif()
    # Hash checks
    if (NOT OLD_HASHES STREQUAL NEW_HASHES)
        foreach(F OLD NEW IN ZIP_LISTS OLD_FILES OLD_HASHES NEW_HASHES)
            if (NOT OLD STREQUAL NEW)
                message(FATAL_ERROR "File ${ROOT}${F}'s hash is wrong.\n${ERR_MSG}")
            endif()
        endforeach()
        message(FATAL_ERROR "Hashes differ but cannot figure out how.\n${ERR_MSG}") # This should not happen
    endif()
endfunction()

function(hash_dir_store_check ROOT ERR_MSG) # Runs store if not run before, else check
    set (FH "${ROOT}/${HASHES_FNAME}")
    set (FF "${ROOT}/${FILES_FNAME}")
    if (EXISTS "${FH}" OR EXISTS "${FF}") # Hashes should exist
        if (EXISTS "${FH}" AND EXISTS "${FF}")
            message(STATUS "Validating hashes for ${ROOT}")
            hash_dir_check("${ROOT}" "${ERR_MSG}")
        else()
            message(FATAL_ERROR "Saved files/hashes files have been corrupted") # Should not happen
        endif()
    else() # No hashes generated previously
        message("Calculating and storing hashes for ${ROOT}")
        hash_dir_store("${ROOT}")
    endif()
endfunction()
