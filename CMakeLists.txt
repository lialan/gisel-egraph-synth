# gisel-egraph-synth: the GlobalISel e-graph combiner, the corpus extractor of
# the rule synthesizer and the combiners of the synthesized rules, built
# against the stock LLVM of third_party/llvm-project into bin/llc (the stock
# llc driver with these passes).
#
#   scripts/build-llvm.sh   builds LLVM into build/llvm
#   scripts/build.sh        builds this project into build/plugin
cmake_minimum_required(VERSION 3.20)
project(GISelEGraphSynth LANGUAGES C CXX)

find_package(LLVM REQUIRED CONFIG)
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")
if(NOT DEFINED LLVM_BUILD_MAIN_SRC_DIR)
  message(FATAL_ERROR "Use the LLVM build tree (build/llvm), not an install")
endif()

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(LLVM_RUNTIME_OUTPUT_INTDIR ${CMAKE_BINARY_DIR}/bin)
set(LLVM_LIBRARY_OUTPUT_INTDIR ${CMAKE_BINARY_DIR}/lib)
set(LLVM_TABLEGEN_EXE "${LLVM_TOOLS_BINARY_DIR}/llvm-tblgen")
list(APPEND CMAKE_MODULE_PATH "${LLVM_CMAKE_DIR}")
include(TableGen)
include(AddLLVM)
include(HandleLLVMOptions)

include_directories(${LLVM_INCLUDE_DIRS})
include_directories(${PROJECT_SOURCE_DIR}/include)
include_directories(${PROJECT_BINARY_DIR}/lib)
separate_arguments(LLVM_DEFINITIONS_LIST NATIVE_COMMAND ${LLVM_DEFINITIONS})
add_definitions(${LLVM_DEFINITIONS_LIST})

# The combiners of the synthesized rules (lib/SynthCombiners.td).
set(LLVM_TARGET_DEFINITIONS lib/SynthCombiners.td)
set(SYNTH_TD_DEPENDS ${PROJECT_SOURCE_DIR}/td/GISynthCombines.td)
foreach(target AMDGPU AArch64)
  set(extra)
  if(target STREQUAL "AMDGPU")
    # The same LLT encoding as the AMDGPU combiners.
    set(extra -gisel-extended-llt)
  endif()
  llvm_tablegen(lib/GISynth${target}Combiner.inc
    -gen-global-isel-combiner -combiners=GISynth${target}Combiner ${extra}
    EXTRA_INCLUDES ${PROJECT_SOURCE_DIR}/td
    DEPENDS ${SYNTH_TD_DEPENDS})
endforeach()
add_public_tablegen_target(GISynthCombinersGen)

set(GISELEGRAPHSYNTH_SOURCES
  lib/GIEGraph.cpp
  lib/GIEGraphCombiner.cpp
  lib/GIEGraphRules.cpp
  lib/GISynthCorpusExtractor.cpp
  lib/SynthCombinerAMDGPU.cpp
  lib/SynthCombinerAArch64.cpp
  )

# The sources, compiled once for bin/llc and the unit tests.
add_library(GISelEGraphSynthObjects OBJECT ${GISELEGRAPHSYNTH_SOURCES})
add_dependencies(GISelEGraphSynthObjects GISynthCombinersGen)
llvm_update_compile_flags(GISelEGraphSynthObjects)

# bin/llc: the stock llc driver of the submodule (llc.cpp and the
# LLVMLlcDriver sources) with the passes of this project linked in. The
# object files are linked directly, so the static registration objects of
# lib/PassRegistration.cpp are kept.
set(LLC_SRC ${LLVM_BUILD_MAIN_SRC_DIR}/tools/llc)
set(LLVM_LINK_COMPONENTS
  AllTargetsAsmParsers AllTargetsCodeGens AllTargetsDescs AllTargetsInfos
  Analysis AsmPrinter CodeGen CodeGenTypes Core GlobalISel IPO IRPrinter
  IRReader MC MIRParser Passes Plugins Remarks ScalarOpts SelectionDAG
  Support Target TargetParser TransformUtils Vectorize)
add_llvm_executable(gisel-egraph-synth-llc
  ${LLC_SRC}/llc.cpp
  ${LLC_SRC}/lib/llcdriver.cpp
  ${LLC_SRC}/lib/NewPMDriver.cpp
  lib/PassRegistration.cpp
  $<TARGET_OBJECTS:GISelEGraphSynthObjects>
  DEPENDS GISynthCombinersGen
  )
set_target_properties(gisel-egraph-synth-llc PROPERTIES OUTPUT_NAME llc)
target_include_directories(gisel-egraph-synth-llc PRIVATE ${LLC_SRC}/lib)

option(GISELEGRAPHSYNTH_INCLUDE_TESTS "Build the unit tests and lit tests" ON)
if(GISELEGRAPHSYNTH_INCLUDE_TESTS)
  add_subdirectory(unittests)
  add_subdirectory(test)
endif()
