########################################################################
# Build stuff
########################################################################

include_directories(${CMAKE_CURRENT_SOURCE_DIR})
include_directories(${LIBSDRPLAY_INCLUDE_DIRS})

#enable c++11 features
#if(CMAKE_COMPILER_IS_GNUCXX)
#
#    #C++11 is a required language feature for this project
#    include(CheckCXXCompilerFlag)
#    CHECK_CXX_COMPILER_FLAG("-std=c++11" HAS_STD_CXX11)
#    if(HAS_STD_CXX11)
#        set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++11")
#    else(HAS_STD_CXX11)
#        set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++0x")
#    endif()

#    #disable warnings for unused parameters
#    add_definitions(-Wno-unused-parameter)

#endif(CMAKE_COMPILER_IS_GNUCXX)

add_library(ExtIO_SDRPlay MODULE ExtIO_SDRplay.h ExtIO_SDRplay.cpp)
target_link_libraries(ExtIO_SDRPlay ${LIBSDRPLAY_LIBRARIES})
set_target_properties(ExtIO_SDRPlay PROPERTIES DEBUG_POSTFIX "") #same name in debug mode

