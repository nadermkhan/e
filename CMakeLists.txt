cmake_minimum_required(VERSION 3.20)
project(ElegantCompiler LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# 1. Find LLVM
find_package(LLVM REQUIRED CONFIG)
message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")

include_directories(${LLVM_INCLUDE_DIRS})
# REMOVED: add_definitions(${LLVM_DEFINITIONS}) -> This was causing the MSYS2 stray quote bug

# 2. Build the Evo Parser Generator (No LLVM needed for this!)
add_executable(evo evo.cpp)

# 3. Custom Command: Run evo to generate ElegantParser.hpp
add_custom_command(
    OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/ElegantParser.hpp
    COMMAND evo ${CMAKE_CURRENT_SOURCE_DIR}/elegant.evo -o ${CMAKE_CURRENT_BINARY_DIR}/ElegantParser.hpp
    DEPENDS evo ${CMAKE_CURRENT_SOURCE_DIR}/elegant.evo
    COMMENT "Generating ElegantParser.hpp from elegant.evo..."
)

# 4. Build the actual Elegant Compiler (elegantc)
add_executable(elegantc main.cpp ${CMAKE_CURRENT_BINARY_DIR}/ElegantParser.hpp)

# Tell CMake to link the specific LLVM modules
llvm_map_components_to_libnames(llvm_libs Core ExecutionEngine OrcJIT Support Target native)
target_link_libraries(elegantc PRIVATE ${llvm_libs})

# FEATURE: Cross-platform Thread shims — the weak C-linkage stubs
# (_beginthread, Sleep, WaitForSingleObject) in main.cpp must be
# visible to LLJIT's process-symbol generator on POSIX hosts so the
# Prelude's Thread class can JIT even on Linux/macOS, where the Win32
# APIs don't exist. On non-Windows we export all symbols; on Windows
# the real msvcrt/kernel32 symbols resolve through the usual channels
# and we don't need to alter visibility.
if(NOT WIN32)
    set_target_properties(elegantc PROPERTIES ENABLE_EXPORTS ON)
    target_link_options(elegantc PRIVATE -rdynamic)
endif()

# Add the binary dir to includes so main.cpp can find ElegantParser.hpp
target_include_directories(elegantc PRIVATE ${CMAKE_CURRENT_BINARY_DIR})
