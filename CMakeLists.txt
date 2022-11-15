cmake_minimum_required(VERSION 3.23)
project(block_img_zhangwenbo)

set(CMAKE_CXX_STANDARD 14)
include_directories(include)
include_directories(/usr/local/include)
include_directories(hashlibpp-master/build/include)


if(MSVC)
#    add_definitions(-D_CRT_SECURE_NO_WARNINGS)
    add_definitions(_CRT_SECURE_NO_WARNINGS)
endif()

add_executable(block_img_zhangwenbo main.cpp)
#target_link_libraries(block_img_zhangwenbo pbc gmp libgmp)