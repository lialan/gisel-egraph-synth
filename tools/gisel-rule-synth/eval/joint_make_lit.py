#!/usr/bin/env python3
"""Writes the inputs of test/Joint/joint-rules-<target>.mir: the gMIR that
the pre-legalizer combiner leaves for the difference of squares and for
x*(y+1), x*(y-1) (see eval/joint_validate.py), and mutations of it. The
IR module only carries the attributes of the arguments (noundef), which
the guard defined(x) reads. The CHECK lines are added with
llvm/utils/update_mir_test_checks.py.

  joint_make_lit.py --out test/Joint
"""

import argparse
from pathlib import Path

ap = argparse.ArgumentParser()
ap.add_argument('--out', required=True, type=Path)
args = ap.parse_args()
args.out.mkdir(parents=True, exist_ok=True)

TARGETS = {
    'amdgpu': ('-mtriple=amdgpu11.00-amd-amdhsa -mcpu=gfx1100',
               ('$vgpr0', '$vgpr1'), 'SI_RETURN'),
    'aarch64': ('-mtriple=aarch64', ('$w0', '$w1'), 'RET_ReallyLR'),
}

DSQ = [
    '%0:_(i32) = COPY {a0}',
    '%1:_(i32) = COPY {a1}',
    '%2:_(i32) = G_MUL %0, %0',
    '%3:_(i32) = G_SUB %0, %1',
    '%4:_(i32) = G_ADD %1, %0',
    '%5:_(i32) = G_MUL %3, %4',
    '{a0} = COPY %2(i32)',
    '{a1} = COPY %5(i32)',
    '{ret} implicit {a0}, implicit {a1}',
]

HELPER = [
    '%0:_(i32) = COPY {a0}',
    '%1:_(i32) = COPY {a1}',
    '%2:_(i32) = G_CONSTANT i32 {c}',
    '%3:_(i32) = G_ADD %1, %2',
    '%4:_(i32) = G_MUL %3, %0',
    '%5:_(i32) = G_SHL %0, %2(i32)',
    '%6:_(i32) = G_SUB %4, %5',
    '{a0} = COPY %4(i32)',
    '{a1} = COPY %6(i32)',
    '{ret} implicit {a0}, implicit {a1}',
]


def replace(lines, old, new):
    assert old in lines, old
    return [new if l == old else l for l in lines]


def cases(target):
    out = [
        ('dsq', True, DSQ,
         'x*x and (x-y)*(x+y): the square stays (its flags are dropped, '
         'a new\n# instruction reads it), y*y is new, the product is '
         'replaced.'),
        ('dsq_commuted', True,
         replace(replace(DSQ, '%4:_(i32) = G_ADD %1, %0',
                         '%4:_(i32) = G_ADD %0, %1'),
                 '%5:_(i32) = G_MUL %3, %4', '%5:_(i32) = G_MUL %4, %3'),
         'Commuted operands.'),
        ('dsq_square_nsw', True,
         replace(DSQ, '%2:_(i32) = G_MUL %0, %0',
                 '%2:_(i32) = nsw G_MUL %0, %0'),
         'The square has nsw: it loses it.'),
        ('dsq_root_nsw', True,
         replace(DSQ, '%5:_(i32) = G_MUL %3, %4',
                 '%5:_(i32) = nsw G_MUL %3, %4'),
         'Flags of an instruction that dies do not matter.'),
        ('dsq_not_noundef', False, DSQ,
         'The arguments are not noundef: defined(x), defined(y) fail.'),
        ('dsq_wrong_add', True,
         replace(DSQ, '%4:_(i32) = G_ADD %1, %0', '%4:_(i32) = G_ADD %1, %1'),
         'Not the region of the rule.'),
        ('dsq_extra_user', True,
         replace(replace(DSQ, '%5:_(i32) = G_MUL %3, %4',
                         '%5:_(i32) = G_MUL %3, %4\n    '
                         '%6:_(i32) = G_XOR %5, %3'),
                 '{a1} = COPY %5(i32)', '{a1} = COPY %6(i32)'),
         'x - y has another user: it would not die.'),
        ('dsq_square_after_root', True,
         [l for l in DSQ if l != '%2:_(i32) = G_MUL %0, %0'][:5] +
         ['%2:_(i32) = G_MUL %0, %0'] +
         [l for l in DSQ if l != '%2:_(i32) = G_MUL %0, %0'][5:],
         'The square is after the product, before its users: the new\n'
         '# instructions are placed after the square.'),
        ('dsq_square_after_use', True,
         ['%0:_(i32) = COPY {a0}', '%1:_(i32) = COPY {a1}',
          '%3:_(i32) = G_SUB %0, %1', '%4:_(i32) = G_ADD %1, %0',
          '%5:_(i32) = G_MUL %3, %4', '{a1} = COPY %5(i32)',
          '%2:_(i32) = G_MUL %0, %0', '{a0} = COPY %2(i32)',
          '{ret} implicit {a0}, implicit {a1}'],
         'The square is after a user of the product: no position follows '
         'the\n# square and dominates that user.'),
    ]
    if target == 'amdgpu':
        out += [
            ('helper', True, [l.replace('{c}', '1') for l in HELPER],
             'x*(y+1), x*(y-1) after opt -O2: one new x*y for both '
             'outputs.'),
            ('helper_two', True, [l.replace('{c}', '2') for l in HELPER],
             'The constant is 2, not 1: not the rule.'),
        ]
    return out


for target, (flags, (a0, a1), ret) in TARGETS.items():
    cs = cases(target)
    text = ['# RUN: llc %s -run-pass=gisynth-joint-combiner %%s -o - '
            '| FileCheck %%s' % flags, '',
            '# The joint region rules of td/GISynthJointCombines.td: found '
            'by the generic',
            '# search of tools/gisel-rule-synth (joint-search), proved and '
            'emitted by',
            '# joint-emit. Each function is a rewrite or a region that the '
            'matcher',
            '# must reject.', '', '--- |']
    for name, noundef, _, _ in cs:
        nu = 'noundef ' if noundef else ''
        text.append('  define { i32, i32 } @%s(i32 %s%%x, i32 %s%%y) {'
                    % (name, nu, nu))
        text.append('    ret { i32, i32 } poison')
        text.append('  }')
    text.append('...')
    for name, _, lines, comment in cs:
        text += ['', '# ' + comment, '---', 'name: %s' % name,
                 'tracksRegLiveness: true', 'body: |', '  bb.0:',
                 '    liveins: %s, %s' % (a0, a1), '']
        text += ['    ' + l.format(a0=a0, a1=a1, ret=ret) for l in lines]
        text.append('...')
    (args.out / ('joint-rules-%s.mir' % target)).write_text(
        '\n'.join(text) + '\n')
print('ok')
