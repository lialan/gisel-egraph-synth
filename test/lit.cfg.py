# -*- Python -*-
# Lit tests. `llc` in a RUN line is bin/llc of this project (first in PATH):
# the stock llc driver with the passes of this project. The other tools
# (FileCheck, not, ...) come from the stock LLVM build.

import os

import lit.formats

config.name = "GISelEGraphSynth"
config.test_format = lit.formats.ShTest(execute_external=False)
config.suffixes = [".mir", ".ll"]
config.test_source_root = os.path.dirname(__file__)

path = [config.plugin_bin_dir, config.llvm_tools_dir]
config.environment["PATH"] = os.pathsep.join(
    path + [config.environment.get("PATH", os.environ.get("PATH", ""))]
)

# test/SynthChain checks rules that a scratch build of
# tools/gisel-rule-synth/eval/rule_chain.py compiles in (not the selected
# rules of td/GISynthCombines.td): it runs them with --param synth_chain=1.
if lit_config.params.get("synth_chain"):
    config.available_features.add("synth-chain")
