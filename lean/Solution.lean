module
-- SPDX-License-Identifier: Apache-2.0

public import Challenge
public import Catalytic

/-!
# Verified Solutions to All 18 Formalized Theorems (`T1`–`T4`, Corollaries, and Soundness Bridges)

All proofs are kernel-checked in pure Lean 4.35.0 with zero external dependencies and only the three standard Lean axioms.
-/

namespace Catalytic.Solution

open Catalytic.Challenge

public theorem t1_digit_sum_dichotomy : T1_DigitSumDichotomy :=
  fun p t hp ht f => rp_pass_two_iff p t hp ht f

public theorem t1a_two_access_frobenius_collapse : T1a_TwoAccessFrobeniusCollapse :=
  fun p m hp => char_p_two_access_unbounded_degree p m hp

public theorem t1b_f2_saturation : T1b_F2Saturation :=
  fun t => char_2_two_reg_x3_impossible t

public theorem t1c_impossibility_threshold : T1c_ImpossibilityThreshold :=
  fun p d t hp hd ht hs => char_p_impossibility_threshold p d t hp hd ht hs

public theorem t1d_vinciguerra_recovery : T1d_VinciguerraRecovery :=
  fun p d t hp hd2 hdp ht => char_p_large_recovers_vinciguerra_thm35 p d t hp hd2 hdp ht

public theorem t1e_extension_field_separation : T1e_ExtensionFieldSeparation :=
  ⟨gf4_x5_in_3_accesses, gf4_x5_not_in_2_accesses,
   gf4_x3_in_4_accesses, gf4_x3_not_in_3_accesses,
   gf4_x7_impossible_all_t⟩

public theorem t1s_pass2_ring_soundness : T1s_Pass2RingSoundness :=
  ⟨fun R _ _ hchar prog D hD o u x =>
     Pass2Prog.execRing_eq_evalState2 (R := R) hchar prog D hD o u x,
   fun _ _ _ hclean R _ hchar o u x =>
     pass2_clean_implies_ring_exec hclean R hchar o u x⟩

public theorem t1es_pass2_gf4_soundness : T1es_Pass2GF4Soundness :=
  ⟨fun R _ φ prog D hD o u x =>
     Pass2GF4Prog.execAlg_eq_evalState2GF4 (R := R) φ prog D hD o u x,
   fun _ _ hclean R _ φ o u x =>
     pass2gf4_clean_implies_alg_exec hclean R φ o u x⟩

public theorem t2_bilinear_frobenius_collapse : T2_BilinearFrobeniusCollapse :=
  fun k hk =>
    ⟨frobBilinProg_accesses k hk,
     frobBilinProg_bilinOps k hk,
     frobBilinProg_valid k hk,
     fun R _ x init => frobBilinProg_clean (R := R) k hk x init⟩

public theorem t2b_distinct_operand_frobenius : T2b_DistinctOperandFrobenius :=
  fun k hk =>
    ⟨frobDistinctProg_accesses k hk,
     frobDistinctProg_valid k hk,
     fun R _ x init => frobDistinctProg_clean (R := R) k hk x init⟩

public theorem t3a_three_reg_5call_x7 : T3a_ThreeReg5CallX7 :=
  fun R _ inv576 hinv => three_reg_5call_x7 (R := R) inv576 hinv

public theorem t3b_three_reg_6call_x9 : T3b_ThreeReg6CallX9 :=
  fun R _ invD hinv => three_reg_6call_x9 (R := R) invD hinv

public theorem t3c_three_reg_7call_x11 : T3c_ThreeReg7CallX11 :=
  fun R _ invD hinv => three_reg_7call_x11 (R := R) invD hinv

public theorem t3d_three_reg_8call_x13 : T3d_ThreeReg8CallX13 :=
  fun R _ invD hinv => three_reg_8call_x13 (R := R) invD hinv

public theorem t3e_exponent_chain : T3e_ExponentChain :=
  exponent_strict_improvement_chain

public theorem t3f_global_integer_optimality : T3f_GlobalIntegerOptimality :=
  exponent_global_integer_optimality

public theorem t3g_three_reg_9call_x15 : T3g_ThreeReg9CallX15 :=
  fun R _ invD hinv => three_reg_9call_x15 (R := R) invD hinv

public theorem t4_balanced_multilinear_product : T4_BalancedMultilinearProduct :=
  fun k target sign pool offset hsign hpool hnd =>
    ⟨by rw [balancedProdProg_length k target sign pool offset hpool]; exact balancedOpCount_formula k,
     balancedProdProg_strictValid k target sign pool offset hsign hpool hnd,
     fun R _ xs st => balancedProdProg_clean (R := R) k target sign pool offset hpool hnd xs st⟩

/-- Single master conjunction bundling all 18 verified theorems for one-shot external kernel export. -/
public theorem prove_all_catalytic_theorems :
    T1_DigitSumDichotomy ∧
    T1a_TwoAccessFrobeniusCollapse ∧
    T1b_F2Saturation ∧
    T1c_ImpossibilityThreshold ∧
    T1d_VinciguerraRecovery ∧
    T1e_ExtensionFieldSeparation ∧
    T1s_Pass2RingSoundness ∧
    T1es_Pass2GF4Soundness ∧
    T2_BilinearFrobeniusCollapse ∧
    T2b_DistinctOperandFrobenius ∧
    T3a_ThreeReg5CallX7 ∧
    T3b_ThreeReg6CallX9 ∧
    T3c_ThreeReg7CallX11 ∧
    T3d_ThreeReg8CallX13 ∧
    T3e_ExponentChain ∧
    T3f_GlobalIntegerOptimality ∧
    T3g_ThreeReg9CallX15 ∧
    T4_BalancedMultilinearProduct :=
  ⟨t1_digit_sum_dichotomy,
   t1a_two_access_frobenius_collapse,
   t1b_f2_saturation,
   t1c_impossibility_threshold,
   t1d_vinciguerra_recovery,
   t1e_extension_field_separation,
   t1s_pass2_ring_soundness,
   t1es_pass2_gf4_soundness,
   t2_bilinear_frobenius_collapse,
   t2b_distinct_operand_frobenius,
   t3a_three_reg_5call_x7,
   t3b_three_reg_6call_x9,
   t3c_three_reg_7call_x11,
   t3d_three_reg_8call_x13,
   t3e_exponent_chain,
   t3f_global_integer_optimality,
   t3g_three_reg_9call_x15,
   t4_balanced_multilinear_product⟩

end Catalytic.Solution
