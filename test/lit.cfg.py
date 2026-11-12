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
