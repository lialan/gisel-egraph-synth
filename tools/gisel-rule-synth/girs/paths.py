"""Locations in the gisel-egraph-synth repository.

The repository holds the plugin sources, this tool and the LLVM submodule
(third_party/llvm-project). Two build directories are used:

  build/llvm    stock LLVM of the submodule (llc, opt, llvm-tblgen, ...).
  build/plugin  bin/llc: the stock llc driver of the submodule with the
                passes of this repository linked in.

Set GIRS_LLVM_BUILD or GIRS_PLUGIN_BUILD to use other build directories.
"""

import os

TOOL = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
REPO = os.path.dirname(os.path.dirname(TOOL))
# The root of the LLVM source tree. Corpus manifests list paths relative to
# it (for example llvm/test/CodeGen/AMDGPU/add.ll).
LLVM_ROOT = os.path.join(REPO, 'third_party', 'llvm-project')
LLVM_BUILD = os.path.abspath(os.environ.get(
    'GIRS_LLVM_BUILD', os.path.join(REPO, 'build', 'llvm')))
PLUGIN_BUILD = os.path.abspath(os.environ.get(
    'GIRS_PLUGIN_BUILD', os.path.join(REPO, 'build', 'plugin')))
# The ninja target of bin/llc.
LLC_TARGET = 'gisel-egraph-synth-llc'
# The generated files that the build of bin/llc reads.
GEN_TD = os.path.join(REPO, 'td', 'GISynthCombines.td')
GEN_INC = os.path.join(REPO, 'include', 'GISelEGraphSynth',
                       'GISynthGeneratedPredicates.inc')


def llvm_tool(name):
    """A tool of the stock LLVM build (opt, FileCheck, ...)."""
    return os.path.join(LLVM_BUILD, 'bin', name)


def llc(build_dir=None):
    """bin/llc of this repository (the stock driver with its passes)."""
    return os.path.join(build_dir or PLUGIN_BUILD, 'bin', 'llc')
