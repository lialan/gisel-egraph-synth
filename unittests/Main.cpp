//===- Main.cpp - main of the unit tests ----------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// The GISelMITest fixtures need the targets, so this main initializes them
// before the tests run, as the main of the upstream GlobalISelTests does.
//
//===----------------------------------------------------------------------===//

#include "GISelMITest.h"

int main(int argc, char **argv) {
  ::testing::InitGoogleTest(&argc, argv);
  initLLVM();
  return RUN_ALL_TESTS();
}
