module
-- SPDX-License-Identifier: Apache-2.0

public import Catalytic

/-!
# Formal Challenge Statements (`T1`–`T4` and Corollaries)

Exported literal theorem specifications for independent audit (Palomar convention).
All proofs live in `Solution.lean` and `Catalytic.*`; this file defines only propositions.
-/

namespace Catalytic.Challenge

@[expose] public section

/-- **T1 (Base-`p` Digit-Sum Dichotomy for `RP^{pass}_{𝔽_p}(2, t)`):**
For every prime `p`, every `t ≥ 1`, and every univariate polynomial `f ∈ 𝔽_p[x]`,
`f ∈ RP^{pass}_{𝔽_p}(2, t)` iff every degree `d ≥ 2` with `[x^d]f ≢ 0 (mod p)`
satisfies `s_p(d) ≤ min (p - 1) (t - 1)`. -/
def T1_DigitSumDichotomy : Prop :=
  ∀ (p t : Nat), IsPrime p → 1 ≤ t → ∀ (f : List Nat),
    InRPPass2 p t f ↔
      ∀ d : Nat, 2 ≤ d → f.getD d 0 % p ≠ 0 →
        digitSum p d ≤ min (p - 1) (t - 1)

/-- **T1a (2-Access Unbounded-Degree Frobenius Collapse):**
For every prime `p` and every `m : Nat`, `x^(p^m) ∈ RP^{pass}_{𝔽_p}(2, 2)`. -/
def T1a_TwoAccessFrobeniusCollapse : Prop :=
  ∀ (p m : Nat), IsPrime p → InRPPass2 p 2 (monomial (p ^ m))

/-- **T1b (Exact `𝔽_2` 2-Register Saturation):**
Over `𝔽_2`, `x^3 ∉ RP^{pass}_{𝔽_2}(2, t)` for every `t : Nat`. -/
def T1b_F2Saturation : Prop :=
  ∀ (t : Nat), ¬ InRPPass2 2 t (monomial 3)

/-- **T1c (Exact Prime-Field Impossibility Threshold):**
If `s_p(d) ≥ p` and `d ≥ 2`, then `x^d ∉ RP^{pass}_{𝔽_p}(2, t)` for all `t ≥ 1`. -/
def T1c_ImpossibilityThreshold : Prop :=
  ∀ (p d t : Nat), IsPrime p → 2 ≤ d → 1 ≤ t → p ≤ digitSum p d →
    ¬ InRPPass2 p t (monomial d)

/-- **T1d (Characteristic-0 Limit Recovering Vinciguerra Theorem 3.5):**
Whenever `2 ≤ d < p` and `t ≥ 1`, `x^d ∈ RP^{pass}_{𝔽_p}(2, t) ↔ d + 1 ≤ t`. -/
def T1d_VinciguerraRecovery : Prop :=
  ∀ (p d t : Nat), IsPrime p → 2 ≤ d → d < p → 1 ≤ t →
    (InRPPass2 p t (monomial d) ↔ d + 1 ≤ t)

/-- **T2 (Strictly Bilinear 2-Access Frobenius Collapse over Characteristic 2):**
For every `k ≥ 1`, there is a passive-output strictly bilinear register program on `k + 1`
registers using ONLY 2 input accesses and `4*k - 2` bilinear ops that cleanly computes
`x^(2^k)` over EVERY characteristic-2 commutative ring `R`. -/
def T2_BilinearFrobeniusCollapse : Prop :=
  ∀ (k : Nat) (hk : 1 ≤ k),
    BilinProg.accesses (frobBilinProg k hk) = 2 ∧
    BilinProg.bilinOps (frobBilinProg k hk) = 4 * k - 2 ∧
    (∀ instr ∈ frobBilinProg k hk, instr.isValidPassive) ∧
    ∀ (R : Type) [Char2CRing R] (x : R) (init : Fin (k + 1) → R),
      let final := BilinProg.exec x (frobBilinProg k hk) init
      final ⟨0, by omega⟩ = init ⟨0, by omega⟩ + CRing.pow x (2 ^ k) ∧
      ∀ i : Fin (k + 1), i.val ≠ 0 → final i = init i

/-- **T3a (`x^7 ∈ RP^{pass}_R(3, 5)` whenever `576` is invertible, i.e. `char ≠ 2, 3`):** -/
def T3a_ThreeReg5CallX7 : Prop :=
  ∀ (R : Type) [CRing R] (inv576 : R), inv576 * CRing.intCast 576 = 1 →
    Pass3Prog.accesses (Pass3Prog.scaleOut inv576 prog5_x7) = 5 ∧
    ∀ x o u v : R,
      Pass3Prog.exec x (Pass3Prog.scaleOut inv576 prog5_x7) (o, u, v) = (o + CRing.pow x 7, u, v)

/-- **T3b (`x^9 ∈ RP^{pass}_R(3, 6)` whenever `382500000` is invertible, i.e. `char ∉ {2,3,5,17}`):** -/
def T3b_ThreeReg6CallX9 : Prop :=
  ∀ (R : Type) [CRing R] (invD : R), invD * CRing.intCast 382500000 = 1 →
    Pass3Prog.accesses (Pass3Prog.scaleOut invD prog6_x9) = 6 ∧
    ∀ x o u v : R,
      Pass3Prog.exec x (Pass3Prog.scaleOut invD prog6_x9) (o, u, v) = (o + CRing.pow x 9, u, v)

/-- **T3c (`x^11 ∈ RP^{pass}_R(3, 7)` over `ℚ` and good prime fields):** -/
def T3c_ThreeReg7CallX11 : Prop :=
  ∀ (R : Type) [CRing R] (invD : R), invD * CRing.intCast 68724637549388656012800 = 1 →
    Pass3Prog.accesses (Pass3Prog.scaleOut invD prog7_x11) = 7 ∧
    ∀ x o u v : R,
      Pass3Prog.exec x (Pass3Prog.scaleOut invD prog7_x11) (o, u, v) = (o + CRing.pow x 11, u, v)

/-- **T3d (`x^13 ∈ RP^{pass}_R(3, 8)` — optimal 3-register exponent `log_13 8 ≈ 0.810714`):** -/
def T3d_ThreeReg8CallX13 : Prop :=
  ∀ (R : Type) [CRing R] (invD : R), invD * CRing.intCast 2656207148788801777680 = 1 →
    Pass3Prog.accesses (Pass3Prog.scaleOut invD prog8_x13) = 8 ∧
    ∀ x o u v : R,
      Pass3Prog.exec x (Pass3Prog.scaleOut invD prog8_x13) (o, u, v) = (o + CRing.pow x 13, u, v)

/-- **T3e (Exact Rational Separation of Strictly Decreasing Exponents):**
`log_13 8 < 30/37 < log_11 7 < 13/16 < log_9 6 < 9/11 < log_7 5 < 5/6 < log_5 4`
and `log_13 8 < 30/37 < log_15 9`. -/
def T3e_ExponentChain : Prop :=
  (8 ^ 37 < 13 ^ 30) ∧ (11 ^ 30 < 7 ^ 37) ∧
  (7 ^ 16 < 11 ^ 13) ∧ (9 ^ 13 < 6 ^ 16) ∧
  (6 ^ 11 < 9 ^ 9)   ∧ (7 ^ 9 < 5 ^ 11) ∧
  (5 ^ 6 < 7 ^ 5)    ∧ (5 ^ 5 < 4 ^ 6) ∧
  (15 ^ 30 < 9 ^ 37)

/-- **T4 (Balanced Zero-Workspace Bilinear Multilinear Product):**
For every `k : Nat`, arbitrary commutative ring `R`, inputs `xs`, arbitrary catalytic state `st`,
and distinct register list `target :: pool` (`pool.length ≥ k + 1` for `k ≥ 1`),
`balancedProdProg` cleanly computes `x_0 * ... * x_{2^k - 1}` with strictly distinct indices
and exact op count `3 * ops + 4 = 7 * (2^k)^2`. -/
def T4_BalancedMultilinearProduct : Prop :=
  ∀ (k target : Nat) (sign : Int) (pool : List Nat) (offset : Nat),
    (sign = 1 ∨ sign = -1) →
    (k = 0 ∨ k + 1 ≤ pool.length) →
    (target :: pool).Nodup →
    3 * (balancedProdProg k target sign pool offset).length + 4 = 7 * (2 ^ k) ^ 2 ∧
    (∀ op ∈ balancedProdProg k target sign pool offset, op.isStrictValid) ∧
    ∀ (R : Type) [CRing R] (xs st : Nat → R),
      CatProg.exec xs (balancedProdProg k target sign pool offset) st =
        (fun r => if r = target then st target + CRing.intCast sign * rangeProd xs offset (2 ^ k)
                  else st r)

end

end Catalytic.Challenge
