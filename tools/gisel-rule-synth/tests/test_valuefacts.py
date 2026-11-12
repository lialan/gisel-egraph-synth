"""Generic facts -> discovery -> guarded proof -> emitted matcher coverage.
No hand-authored replacement is fed to the discovery tests. Solver work is
bounded; real extraction uses the one llc build shared by the whole suite.
"""
import importlib.util
import json
import os
from pathlib import Path
import random
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
import z3
from girs import corpus, discover, emit, fp, ir, ops, precond, smt, synth, targets, valuefacts, vector

V = ('var', 0)

def instance(src, width, fact):
    return corpus.Instance(src, (width,), (fact,), [None], [], [], [('fixture', 'test', '%0')])

def synthesized(inst, tgt):
    sy = synth.Synthesizer(smt.Z3Backend(timeout_ms=1500),
                          limits=synth.SynthLimits(max_atoms=3, max_schedules=1,
                              slow_timeout_ms=1500))
    rid = sy.add(inst, tgt)
    if rid is not None:
        sy.finalize([inst])
    return sy, rid


class PrecisionFacts(unittest.TestCase):
    def test_generalization_keeps_a_proved_precision_condition(self):
        src = ('G_FPTOSI',32,('G_SITOFP',32,V))
        inst = instance(src,32,(0xff000000,0))
        cands, stats = discover.discover(inst, smt.Z3Backend(timeout_ms=1500),
            discover.Limits(grammar='auto', max_terms=2000,max_evals=100000))
        self.assertIn(V,[c['tgt'] for c in cands])
        sy,rid=synthesized(inst,V)
        self.assertIsNotNone(rid)
        rule=sy.rules[rid]
        self.assertIn('fitsfp',str(rule['disjuncts']))
        self.assertIsNone(emit.why_not_emittable(rule))
        self.assertIn('knownIntFitsFP',emit._cpp_guard(rule))
        self.assertFalse(valuefacts.fits_fp((0x80000000,0),32,True,32))
        self.assertEqual(ir.evaluate(src,(32,),[2**24+1]),2**24)

    def test_signed_unsigned_trailing_zero_and_exponent_boundaries(self):
        self.assertTrue(valuefacts.fits_fp((0xff000000,0),32,False,32))
        self.assertTrue(valuefacts.fits_fp((0x7f,0),32,True,32))
        self.assertFalse(valuefacts.fits_fp((0,0),32,True,32))
        self.assertFalse(valuefacts.fits_fp((0x7fffffff,0x80000000),32,False,16))
        for signed in (False,True):
            for fw in (16,32,64):
                enc=smt.Encoder((32,))
                f=(0xff000000,0)
                formula=z3.simplify(z3.substitute(valuefacts.z3_fits_fp(enc.kz[0],enc.ko[0],signed,fw),
                       (enc.kz[0],z3.BitVecVal(f[0],32)),(enc.ko[0],z3.BitVecVal(0,32))))
                self.assertEqual(z3.is_true(formula),valuefacts.fits_fp(f,32,signed,fw))

    def test_atom_roundtrip_and_variable_renaming(self):
        atoms=[('fitsfp',2,True,32),('fpclass',2,504),('fpintegral',2),('fprange',2,True,32)]
        for a in atoms:
            self.assertEqual(precond.atom_from_json(precond.atom_to_json(a)),a)
            self.assertEqual(precond.rename_atom(a,{2:0}),(a[0],0)+a[2:])
            self.assertEqual(precond.atom_all_vars(a),[2])


class FloatingFacts(unittest.TestCase):
    def test_roundtrip_needs_range_integrality_and_negative_zero_guard(self):
        src=('G_SITOFP',32,('G_FPTOSI',32,V))
        f=valuefacts.pack((0,0),valuefacts.FINITE & ~valuefacts.NEGZERO,True,
                         fp.from_int(-100,32),fp.from_int(100,32))
        inst=instance(src,32,f)
        cands,_=discover.discover(inst,smt.Z3Backend(timeout_ms=1500),
            discover.Limits(grammar='source',max_terms=1000,max_evals=100000))
        self.assertIn(V,[c['tgt'] for c in cands])
        sy,rid=synthesized(inst,V)
        self.assertIsNotNone(rid)
        rule=sy.rules[rid]
        self.assertIn('getFPValueFacts',emit._cpp_guard(rule))
        # Each failure mode must remain a counterexample, not be sampled away.
        for x in [fp.from_int(1,32)+1,1<<31]:
            self.assertNotEqual(ir.evaluate(src,(32,),[x]),x)
        sat=('G_FPTOSI_SAT',32,V)
        plain=('G_FPTOSI',32,V)
        enc=smt.Encoder((32,))
        guard=precond.z3_pred((('fprange',0,True,32),),enc)
        self.assertEqual(smt.Z3Backend(timeout_ms=1500).check(smt.refinement_violation(enc,sat,plain,guard)).status,'unsat')
        self.assertEqual(discover.prove_concrete(instance(sat,32,(0,0)),plain,
                         smt.Z3Backend(timeout_ms=1500)).status,'sat')

    def test_vector_fact_requires_every_lane(self):
        ty=ops.vec(2,32)
        src=('G_SITOFP',ty,('G_FPTOSI',ty,V))
        guard=[(('fpintegral',0),('fprange',0,True,16),('fpclass',0,1023^32))]
        f,_,_=vector.violation(src,V,(ty,),dnf=guard)
        self.assertEqual(smt.Z3Backend(timeout_ms=1500).check(f).status,'unsat')
        # Leaving negative zero unconstrained fails on either lane.
        f,_,_=vector.violation(src,V,(ty,),dnf=[guard[0][:-1]])
        self.assertEqual(smt.Z3Backend(timeout_ms=1500).check(f).status,'sat')

    def test_old_facts_unknown_and_samples_respect_new_facts(self):
        self.assertFalse(precond.eval_atom(('fpintegral',0),((0,0),),(32,)))
        f=valuefacts.pack((0,0),504,True,fp.from_int(-100,32),fp.from_int(100,32))
        inst=instance(('G_FPTOSI',32,V),32,f)
        for env in discover.sample_envs(inst,32,random.Random(42)):
            self.assertTrue(valuefacts.permits(f,env[0],32))
        for x in [fp.qnan(32),fp.inf(32),fp.from_int(101,32)]:
            self.assertFalse(discover.consistent((x,),inst))


class TypesAndLegality(unittest.TestCase):
    def test_type_palette_and_materialized_type(self):
        src=('G_FPTOSI',32,('G_FPEXT',64,('G_SITOFP',16,V)))
        inst=instance(src,32,(0,0))
        old=discover.signature(inst)[1]
        new=discover.signature(inst,discover.Limits(expand_types=True))[1]
        self.assertNotIn((32,'f'),old)
        self.assertIn((32,'f'),new)
        r={'id':'probe','vw':[32], 'source_json':ir.to_json(src),
           'replacement_json':ir.to_json(('G_FPTOSI',32,('G_SITOFP',32,V))),
           'source':'','replacement':''}
        self.assertIsNone(emit.why_not_emittable(r))
        self.assertIn('makeSynthType',emit._cpp_apply(r))
        self.assertTrue(any('G_SITOFP' in c for c in emit._legality_checks(r)))
        r['replacement_json'] = ir.to_json(('lit',32,'0'))
        self.assertTrue(any('isLegalSynthConstant' in c for c in emit._legality_checks(r)))

    def test_scalar_legality_rejects_unsupported_and_unknown(self):
        src=('G_SITOFP',32,('G_ZEXT',32,V))
        inst=instance(src,8,(0,0))
        for action in ('Unsupported',None,'Legal'):
            rows={} if action is None else {'32,8':action}
            cap=targets.Capability({'operators':{'G_UITOFP':rows},
                'type_operands':{'G_UITOFP':[0,1]}})
            cands,_=discover.discover(inst,smt.Z3Backend(timeout_ms=1500),
                discover.Limits(grammar='auto',capability=cap,max_terms=2000,max_evals=100000))
            self.assertEqual(('G_UITOFP',32,V) in [c['tgt'] for c in cands],action=='Legal')
        cap=targets.Capability({'operators':{'G_UITOFP':{'32,8':'WidenScalar'}},
                'type_operands':{'G_UITOFP':[0,1]}})
        n=('G_UITOFP',32,V)
        self.assertTrue(cap.can_create(n,(8,),'pre-legalizer'))
        self.assertFalse(cap.can_create(n,(8,),'post-legalizer'))


LLC=os.environ.get('GIRS_LLC','')
@unittest.skipUnless(LLC and os.path.exists(LLC),'set GIRS_LLC for extraction')
class Extraction(unittest.TestCase):
    def test_actual_compiler_facts_reach_synthesized_guard(self):
        spec=importlib.util.spec_from_file_location('facts_cli',ROOT/'gi-rule-synth.py')
        cli=importlib.util.module_from_spec(spec);spec.loader.exec_module(cli)
        mir="""---
name: fp_facts
tracksRegLiveness: true
body: |
  bb.0:
    liveins: $vgpr0
    %0:_(i32) = COPY $vgpr0
    %1:_(i32) = G_CONSTANT i32 65535
    %2:_(i32) = G_AND %0, %1
    %3:_(f32) = G_UITOFP %2
    %4:_(i32) = G_FPTOUI %3
    %5:_(f32) = G_UITOFP %4
    $vgpr0 = COPY %5
    SI_RETURN implicit $vgpr0
...
"""
        with tempfile.TemporaryDirectory() as tmp:
            path=Path(tmp)/'facts.mir';path.write_text(mir)
            legality = str(Path(tmp)/'legality.json')
            _,out=cli._extract_one(LLC,str(path),tmp,'mir',targets.get('AMDGPU'),
                                  ['-gisel-synth-legality='+legality])
            cap = targets.Capability.load(legality)
            self.assertEqual(cap.node_types(('G_UITOFP',32,V),(16,)), ['f32','i16'])
            self.assertTrue(cap.can_create(('G_UITOFP',32,V),(16,)))
            self.assertFalse(cap.can_create(('G_UITOFP',8,V),(16,)))
            self.assertTrue(out)
            insts,_=corpus.load([out])
            inst=next(i for i in insts if i.expr==('G_UITOFP',32,('G_FPTOUI',32,V)))
            self.assertTrue(valuefacts.fields(inst.facts[0])[1])
            self.assertIsNotNone(valuefacts.fields(inst.facts[0])[2])
            sy,rid=synthesized(inst,V)
            self.assertIsNotNone(rid)
            self.assertIn('getFPValueFacts',emit._cpp_guard(sy.rules[rid]))

if __name__=='__main__':
    unittest.main()
