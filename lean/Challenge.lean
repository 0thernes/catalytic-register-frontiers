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

/-- **T1e (Exact Sharp `𝔽_4` Extension-Field Separation):**
Over the non-prime extension field `𝔽_4 = 𝔽_2[ω]/(ω^2 + ω + 1)`:
  1. `x^5 ∈ RP^{pass}_{𝔽_4}(2, 3)` AND `x^5 ∉ RP^{pass}_{𝔽_4}(2, 2)` (exact `t_min(5) = 3`),
  2. `x^3 ∈ RP^{pass}_{𝔽_4}(2, 4)` AND `x^3 ∉ RP^{pass}_{𝔽_4}(2, 3)` (exact `t_min(3) = 4`),
  3. `∀ t, x^7 ∉ RP^{pass}_{𝔽_4}(2, t)` (unconditional impossibility barrier in `𝔽_4`). -/
def T1e_ExtensionFieldSeparation : Prop :=
  InRPPass2GF4 3 (monomialGF4 5) ∧
  ¬ InRPPass2GF4 2 (monomialGF4 5) ∧
  InRPPass2GF4 4 (monomialGF4 3) ∧
  ¬ InRPPass2GF4 3 (monomialGF4 3) ∧
  (∀ t : Nat, ¬ InRPPass2GF4 t (monomialGF4 7))

/-- **T1s (Literal `CRing` Soundness Bridge for `T1`):**
For EVERY program `prog`, EVERY modulus `p`, and EVERY commutative ring `R` of characteristic `p`
(`natCast p = 0`), literal ring execution `Pass2Prog.execRing` agrees identically with symbolic
`Pass2Prog.exec`, and `CleanlyComputes2 p prog f` implies literal clean execution
`Pass2Prog.execRing x prog (o, u) = (o + evalPolyR f x, u)` for all `o, u, x : R`. -/
def T1s_Pass2RingSoundness : Prop :=
  (∀ (R : Type) [CRing R] (p : Nat), (CRing.natCast p : R) = 0 →
    ∀ (prog : List Pass2Instr) (D : Nat), Pass2Prog.maxDeg prog ≤ D →
      ∀ o u x : R,
        Pass2Prog.execRing x prog (o, u) =
          let st := Pass2Prog.exec p prog
          (o + evalState2Coeff D st.coeff u x, u + CRing.natCast st.b + CRing.natCast st.a * x)) ∧
  (∀ (p : Nat) (prog : List Pass2Instr) (f : List Nat), CleanlyComputes2 p prog f →
    ∀ (R : Type) [CRing R], (CRing.natCast p : R) = 0 →
      ∀ o u x : R, Pass2Prog.execRing x prog (o, u) = (o + evalPolyR f x, u))

/-- **T1es (Literal `GF4`-Algebra Soundness Bridge for `T1e`):**
For EVERY program `prog` and EVERY commutative `GF4`-algebra `(R, φ)` (including `R = GF4` via `GF4Hom.id`),
literal algebra execution `Pass2GF4Prog.execAlg` agrees identically with symbolic `Pass2GF4Prog.exec`,
and `CleanlyComputes2GF4 prog f` implies literal clean execution
`Pass2GF4Prog.execAlg φ x prog (o, u) = (o + evalPolyGF4Alg φ f x, u)` for all `o, u, x : R`. -/
def T1es_Pass2GF4Soundness : Prop :=
  (∀ (R : Type) [CRing R] (φ : GF4Hom R) (prog : List Pass2GF4Instr) (D : Nat),
    Pass2GF4Prog.maxDeg prog ≤ D →
      ∀ o u x : R,
        Pass2GF4Prog.execAlg φ x prog (o, u) =
          let st := Pass2GF4Prog.exec prog
          (o + evalState2GF4Coeff φ D st.coeff u x, u + φ.toFun st.b + φ.toFun st.a * x)) ∧
  (∀ (prog : List Pass2GF4Instr) (f : List GF4), CleanlyComputes2GF4 prog f →
    ∀ (R : Type) [CRing R] (φ : GF4Hom R) (o u x : R),
      Pass2GF4Prog.execAlg φ x prog (o, u) = (o + evalPolyGF4Alg φ f x, u))

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

/-- **T2b (Strictly Distinct-Operand 2-Access Frobenius Collapse over Characteristic 2):**
Adding one swap catalyst (`k + 2` registers total) eliminates ALL self-squares `R_a * R_a`
(strictly pairwise-distinct bilinear operands `dst ≠ a ∧ dst ≠ b ∧ a ≠ b` plus passive linear copies)
while keeping exact cleanliness and **ONLY 2 input accesses** for `x^(2^k)` over every `Char2CRing`. -/
def T2b_DistinctOperandFrobenius : Prop :=
  ∀ (k : Nat) (hk : 1 ≤ k),
    DistinctBilinProg.accesses (frobDistinctProg k hk) = 2 ∧
    (∀ instr ∈ frobDistinctProg k hk, instr.isStrictValidPassive) ∧
    ∀ (R : Type) [Char2CRing R] (x : R) (init : Fin (k + 2) → R),
      let final := DistinctBilinProg.exec x (frobDistinctProg k hk) init
      final ⟨0, by omega⟩ = init ⟨0, by omega⟩ + CRing.pow x (2 ^ k) ∧
      ∀ i : Fin (k + 2), i.val ≠ 0 → final i = init i

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

/-- **T3f (Unconditional Global Integer Optimality of `t = 8` for All `t ≥ 4`):**
Via the single rational separator `30 / 37`, certifies
`log_13 8 < 30 / 37 < log_{2t - 3} t` for EVERY integer `t ≥ 4` with `t ≠ 8`. -/
def T3f_GlobalIntegerOptimality : Prop :=
  (8 ^ 37 < 13 ^ 30) ∧
  (∀ t : Nat, 4 ≤ t → t ≠ 8 → (2 * t - 3) ^ 30 < t ^ 37)

/-- **T3g (`x^15 ∈ RP^{pass}_R(3, 9)` — post-minimum ascent point `log_15 9 ≈ 0.811368`):** -/
def T3g_ThreeReg9CallX15 : Prop :=
  ∀ (R : Type) [CRing R] (invD : R),
    invD * CRing.intCast 876702103804656272895371895753963647960420947968000 = 1 →
    Pass3Prog.accesses (Pass3Prog.scaleOut invD prog9_x15) = 9 ∧
    ∀ x o u v : R,
      Pass3Prog.exec x (Pass3Prog.scaleOut invD prog9_x15) (o, u, v) = (o + CRing.pow x 15, u, v)

/-- **T3h (Four-Register Passive Powering for EVERY `N ≥ 1` via Non-Passive 3-Register Composition + Cook–Mertz):**
For EVERY commutative ring `R` and EVERY `N ≥ 1`:
  1. Using `prog8_x13`, whenever `D_8`, `12!`, and `(ℓ + 1)!` (`ℓ = ⌊log_13 N⌋`) are invertible in `R`,
     there is a literal 4-register passive program computing `O ← O + x^N` cleanly in
     `3 * accesses < 104 * 8^ℓ` (`< (104/3) * N^{log_13 8} = O(N^{0.81072})`).
  2. Using `prog5_x7`, whenever `6!` and `(ℓ + 1)!` (`ℓ = ⌊log_7 N⌋`) are invertible in `R`,
     there is a literal 4-register passive program computing `O ← O + x^N` cleanly in
     `3 * accesses < 70 * 5^ℓ` (`< (70/3) * N^{log_7 5} = O(N^{0.82709})`). -/
def T3h_FourRegPowering : Prop :=
  (∀ (R : Type) [CRing R] (N : Nat) (_ : 1 ≤ N) (invD8 invFact12 invFactLen : R),
    invD8 * CRing.intCast 2656207148788801777680 = 1 →
    invFact12 * CRing.natCast (fact 12) = 1 →
    invFactLen * CRing.natCast (fact (baseDigits 13 (by decide) N).length) = 1 →
    ∃ prog : List (Pass4Instr R),
      let ℓ := (baseDigits 13 (by decide) N).length - 1
      13 ^ ℓ ≤ N ∧
      3 * Pass4Prog.accesses prog < 104 * 8 ^ ℓ ∧
      ∀ x o u r1 r2 : R,
        Pass4Prog.exec x prog (o, u, r1, r2) = (o + CRing.pow x N, u, r1, r2)) ∧
  (∀ (R : Type) [CRing R] (N : Nat) (_ : 1 ≤ N) (invFact6 invFactLen : R),
    invFact6 * CRing.natCast (fact 6) = 1 →
    invFactLen * CRing.natCast (fact (baseDigits 7 (by decide) N).length) = 1 →
    ∃ prog : List (Pass4Instr R),
      let ℓ := (baseDigits 7 (by decide) N).length - 1
      7 ^ ℓ ≤ N ∧
      3 * Pass4Prog.accesses prog < 70 * 5 ^ ℓ ∧
      ∀ x o u r1 r2 : R,
        Pass4Prog.exec x prog (o, u, r1, r2) = (o + CRing.pow x N, u, r1, r2))

/-- **T3i (Algebraic Catalytic Streaming Frequency-Moment Pass Bound over `R^n`):**
Instantiates `T3h` over the pointwise product ring `Fin n → R` (e.g. `𝔽_p^n`): for EVERY
universe size `n`, EVERY commutative ring `R`, and EVERY moment order `D ≥ 1` where `D_8`,
`12!`, and `(⌊log_13 D⌋ + 1)!` are invertible, an explicit 4-vector-register passive program
performs strictly fewer than `(104/3) * 8^ℓ ≤ (8/3) * 13 * D^{log_13 8}` passes over the
frequency vector `f : Fin n → R`, cleanly updates `O_i ← O_i + f_i^D` for all `i : Fin n`,
restores `(U, R1, R2)` identically, and accumulates `F_D(f) = ∑_{i < n} f_i^D` in `sumFin O`. -/
def T3i_StreamingFrequencyMoment : Prop :=
  ∀ (R : Type) [CRing R] (n D : Nat) (_ : 1 ≤ D) (invD8 invFact12 invFactLen : R),
    invD8 * CRing.intCast 2656207148788801777680 = 1 →
    invFact12 * CRing.natCast (fact 12) = 1 →
    invFactLen * CRing.natCast (fact (baseDigits 13 (by decide) D).length) = 1 →
    ∃ prog : List (Pass4Instr (Fin n → R)),
      let ℓ := (baseDigits 13 (by decide) D).length - 1
      13 ^ ℓ ≤ D ∧
      3 * Pass4Prog.accesses prog < 104 * 8 ^ ℓ ∧
      ∀ f o u r1 r2 : Fin n → R,
        let res := Pass4Prog.exec f prog (o, u, r1, r2)
        (∀ i : Fin n, res.1 i = o i + CRing.pow (f i) D) ∧
        res.2 = (u, r1, r2) ∧
        sumFin res.1 = sumFin o + sumFin (fun i => CRing.pow (f i) D)

/-- **T4 (Balanced Zero-Workspace Bilinear Multilinear Product):**
For every `k : Nat`, arbitrary commutative ring `R`, inputs `xs`, arbitrary catalytic state `st`,
and distinct register list `target :: pool` (`pool.length ≥ k + 1` for `k ≥ 1`),
`balancedProdProg` cleanly computes `x_0 * ... * x_{2^k - 1}` with strictly distinct indices,
every operation restricted to the `≤ k + 2` designated registers (`[target]` for `k = 0`,
`target :: pool.take (k + 1)` for `k ≥ 1`), and exact op count `3 * ops + 4 = 7 * (2^k)^2`. -/
def T4_BalancedMultilinearProduct : Prop :=
  ∀ (k target : Nat) (sign : Int) (pool : List Nat) (offset : Nat),
    (sign = 1 ∨ sign = -1) →
    (k = 0 ∨ k + 1 ≤ pool.length) →
    (target :: pool).Nodup →
    let regs := if k = 0 then [target] else target :: pool.take (k + 1)
    3 * (balancedProdProg k target sign pool offset).length + 4 = 7 * (2 ^ k) ^ 2 ∧
    regs.length ≤ k + 2 ∧
    (∀ op ∈ balancedProdProg k target sign pool offset, op.isStrictValid ∧ op.usesOnly regs) ∧
    ∀ (R : Type) [CRing R] (xs st : Nat → R),
      CatProg.exec xs (balancedProdProg k target sign pool offset) st =
        (fun r => if r = target then st target + CRing.intCast sign * rangeProd xs offset (2 ^ k)
                  else st r)

end

end Catalytic.Challenge
