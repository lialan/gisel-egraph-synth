configure_file(${CMAKE_CURRENT_SOURCE_DIR}/lit.site.cfg.py.in
               ${CMAKE_CURRENT_BINARY_DIR}/lit.site.cfg.py @ONLY)

add_custom_target(check-gisel-egraph-synth
  COMMAND ${LLVM_TOOLS_BINARY_DIR}/llvm-lit -sv ${CMAKE_CURRENT_BINARY_DIR}
  COMMAND $<TARGET_FILE:GISelEGraphSynthTests>
  DEPENDS gisel-egraph-synth-llc GISelEGraphSynthTests
  USES_TERMINAL)
