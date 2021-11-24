# Add tests
simple_test(avg)
simple_test(to_hex)
simple_test(bit_mask)
simple_test(stack_limit)
simple_test(fnv1a)
simple_test(strlen)
simple_test(td_false)
simple_test(heap_cache)
simple_test(recurrence_guard)
simple_test(run_on_destruction)
simple_test(run_before_main)
simple_test(run_after_main)

# Add tests with multiple compilation files / extra flags
simple_test(file_line_hash file_line_hash_helper.cpp)

# Add other tests
add_subdirectory(log)
add_subdirectory(type)
add_subdirectory(weak_cache)

# Add more local tests
simple_test(backtrace)
