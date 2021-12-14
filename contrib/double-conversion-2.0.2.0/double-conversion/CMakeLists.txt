cmake_minimum_required(VERSION 2.8)
project(double-conversion)

# pick a version #
set(double-conversion_VERSION 2.0.1)
set(double-conversion_SOVERSION_MAJOR 1)
set(double-conversion_SOVERSION_MINOR 0)
set(double-conversion_SOVERSION_PATCH 0)
set(double-conversion_SOVERSION
  ${double-conversion_SOVERSION_MAJOR}.${double-conversion_SOVERSION_MINOR}.${double-conversion_SOVERSION_PATCH})

# set paths for install -- empty initially
# Offer the user the choice of overriding the installation directories
set(INSTALL_BIN_DIR CACHE PATH "Installation directory for libraries")
set(INSTALL_LIB_DIR CACHE PATH "Installation directory for libraries")
set(INSTALL_INCLUDE_DIR CACHE PATH "Installation directory for include")
# set suffix for CMake files used for packaging
if(WIN32 AND NOT CYGWIN)
  set(INSTALL_CMAKE_DIR CMake)
else()
  set(INSTALL_CMAKE_DIR lib/CMake/double-conversion)
endif()

# Make relative paths absolute (needed later)
foreach(p LIB BIN INCLUDE CMAKE)
  set(var INSTALL_${p}_DIR)
  if(NOT IS_ABSOLUTE "${${var}}")
    set(${var} "${CMAKE_INSTALL_PREFIX}/${${var}}")
  endif()
endforeach()

#
# set up include dirs
include_directories("${PROJECT_SOURCE_DIR}/src"
  "${PROJECT_BINARY_DIR}"
  )

# Add src subdirectory
add_subdirectory(src)

#
# set up testing if requested
option(BUILD_TESTING "Build test programs" OFF)
if(BUILD_TESTING)
  enable_testing()
  include(CTest)
  add_subdirectory(test)
endif()

#
# mention the library target as export library
export(TARGETS double-conversion
  FILE "${PROJECT_BINARY_DIR}/double-conversionLibraryDepends.cmake")

#
# set this build as an importable package
export(PACKAGE double-conversion)

#
# make a cmake file -- in this case, all that needs defining
# is double-conversion_INCLUDE_DIRS
configure_file(double-conversionBuildTreeSettings.cmake.in
  "${PROJECT_BINARY_DIR}/double-conversionBuildTreeSettings.cmake"
  @ONLY)

#
# determine where include is relative to the CMake dir in
# in installed tree
file(RELATIVE_PATH CONF_REL_INCLUDE_DIR "${INSTALL_CMAKE_DIR}"
  "${INSTALL_INCLUDE_DIR}")

#
# sets up config to be used by CMake find_package
configure_file(double-conversionConfig.cmake.in
  "${PROJECT_BINARY_DIR}/double-conversionConfig.cmake"
  @ONLY)
#
# Export version # checked by find_package
configure_file(double-conversionConfigVersion.cmake.in
  "${PROJECT_BINARY_DIR}/double-conversionConfigVersion.cmake"
  @ONLY)
#
# install config files for find_package
install(FILES
  "${PROJECT_BINARY_DIR}/double-conversionConfig.cmake"
  "${PROJECT_BINARY_DIR}/double-conversionConfigVersion.cmake"
  DESTINATION "${INSTALL_CMAKE_DIR}" COMPONENT dev)


#
# generates install cmake files to find libraries in installation.
install(EXPORT double-conversionLibraryDepends DESTINATION
  "${INSTALL_CMAKE_DIR}" COMPONENT dev)
