# Unit tests of the engine and of the guards of the synthesized rules.
set(GTEST_DIR ${LLVM_BUILD_MAIN_SRC_DIR}/../third-party/unittest)
set(LLVM_UNITTEST_DIR ${LLVM_BUILD_MAIN_SRC_DIR}/unittests/CodeGen/GlobalISel)

# The LLVM build tree exports llvm_gtest only in some configurations.
if(NOT TARGET llvm_gtest)
add_library(llvm_gtest STATIC IMPORTED)
set_target_properties(llvm_gtest PROPERTIES
  IMPORTED_LOCATION ${LLVM_LIBRARY_DIR}/libllvm_gtest.a
  INTERFACE_INCLUDE_DIRECTORIES
    "${GTEST_DIR}/googletest/include;${GTEST_DIR}/googlemock/include"
  INTERFACE_COMPILE_DEFINITIONS GTEST_HAS_RTTI=0)
add_library(llvm_gtest_main STATIC IMPORTED)
set_target_properties(llvm_gtest_main PROPERTIES
  IMPORTED_LOCATION ${LLVM_LIBRARY_DIR}/libllvm_gtest_main.a)
endif()

add_executable(GISelEGraphSynthTests
  GIEGraphTest.cpp
  GIEGraphViewsTest.cpp
  GISynthPredicatesTest.cpp
  Main.cpp
  ${LLVM_UNITTEST_DIR}/GISelMITest.cpp
  $<TARGET_OBJECTS:GISelEGraphSynthObjects>
  )
add_dependencies(GISelEGraphSynthTests GISynthCombinersGen)
target_include_directories(GISelEGraphSynthTests PRIVATE ${LLVM_UNITTEST_DIR})
llvm_map_components_to_libnames(GISELEGRAPHSYNTH_TEST_LIBS
  AllTargetsCodeGens AllTargetsDescs AllTargetsInfos AllTargetsAsmParsers
  Analysis AsmParser CodeGen CodeGenTypes Core
  FileCheck GlobalISel MC MIRParser Passes Support Target TargetParser)
target_link_libraries(GISelEGraphSynthTests PRIVATE
  llvm_gtest ${GISELEGRAPHSYNTH_TEST_LIBS})
llvm_update_compile_flags(GISelEGraphSynthTests)
