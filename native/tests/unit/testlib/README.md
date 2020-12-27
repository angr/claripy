This extra layer of indirection exists to protect the top level include space.
CMake includes the top level testlib directory as an include directory.
Since the claricpp headers are also included like this, we use this indirection to force all testlib headers to be under "testlib/".
