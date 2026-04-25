cmake_minimum_required(VERSION 3.27)
project(ida_gekko_pseudocode)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

if(NOT DEFINED ENV{IDASDK})
  set(ENV{IDASDK} "${CMAKE_CURRENT_LIST_DIR}/ida-sdk")
endif()

if(EXISTS "$ENV{IDASDK}/src/cmake/bootstrap.cmake")
  include("$ENV{IDASDK}/src/cmake/bootstrap.cmake")
elseif(EXISTS "$ENV{IDASDK}/cmake/bootstrap.cmake")
  include("$ENV{IDASDK}/cmake/bootstrap.cmake")
else()
  message(FATAL_ERROR "Could not find IDA SDK CMake bootstrap below IDASDK=$ENV{IDASDK}")
endif()

find_package(idasdk REQUIRED)

if(WIN32 AND NOT MSVC)
  message(FATAL_ERROR "ida_gekko_pseudocode is intended to be built with MSVC on Windows")
endif()

ida_add_plugin(ida_gekko_pseudocode
  OUTPUT_NAME
    GekkoHR
  SOURCES
    src/ida_gekko_pseudocode.cpp
  METADATA_JSON
    ida-plugin.json
)

if(MSVC)
  target_compile_options(ida_gekko_pseudocode PRIVATE /permissive- /Zc:__cplusplus)
endif()
