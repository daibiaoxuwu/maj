cmake_minimum_required(VERSION 3.14)
project(maj)

set(CMAKE_CXX_STANDARD 14)

set(CMAKE_CXX_FLAGS_DEBUG "-g")
set(CMAKE_CXX_FLAGS_RELEASE "-O3")
add_executable(maj
        main.cpp)
