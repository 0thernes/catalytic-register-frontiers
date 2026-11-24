module
-- SPDX-License-Identifier: Apache-2.0

import Solution

/-!
# Strict Axiom Allowlist Audit

Every exported theorem in `Catalytic.Solution` (and every non-vacuity witness in
`Catalytic.NonVacuity`) must depend ONLY on a subset of the three standard Lean 4 axioms
`[propext, Classical.choice, Quot.sound]`.
No unproven placeholders, no compiler-trusted reduction, and no custom axioms are permitted.
-/

#print axioms Catalytic.Solution.t1_digit_sum_dichotomy
#print axioms Catalytic.Solution.t1a_two_access_frobenius_collapse
#print axioms Catalytic.Solution.t1b_f2_saturation
#print axioms Catalytic.Solution.t1c_impossibility_threshold
#print axioms Catalytic.Solution.t1d_vinciguerra_recovery
#print axioms Catalytic.Solution.t1e_extension_field_separation
#print axioms Catalytic.Solution.t2_bilinear_frobenius_collapse
#print axioms Catalytic.Solution.t3a_three_reg_5call_x7
#print axioms Catalytic.Solution.t3b_three_reg_6call_x9
#print axioms Catalytic.Solution.t3c_three_reg_7call_x11
#print axioms Catalytic.Solution.t3d_three_reg_8call_x13
#print axioms Catalytic.Solution.t3e_exponent_chain
#print axioms Catalytic.Solution.t3f_global_integer_optimality
#print axioms Catalytic.Solution.t4_balanced_multilinear_product
#print axioms Catalytic.Solution.prove_all_catalytic_theorems
#print axioms Catalytic.NonVacuity.nonvac_all_hypotheses
