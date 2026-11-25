module
-- SPDX-License-Identifier: Apache-2.0

public import Catalytic.CommRing

/-!
# Theorem T3: Strict Improvement Over Vinciguerra's 3-Register Powering Frontier

Vinciguerra (`arXiv:2609.18692`, Theorem 2.3) proved `x^5 ∈ RP^{pass}_K(3, 4)`, yielding
the recursive composition exponent `log_5 4 ≈ 0.861353` for 4-register powering, catalytic
streaming frequency moments (Corollary 5.1.1), and matrix powering (Theorem 5.2).

We construct five explicit passive-output 3-register catalytic programs (in Vinciguerra's
literal Definition 2.2 instruction set) with exact integer coefficients:
  * `prog5_x7`:  5 input accesses, computing `576 * x^7`                  (bad primes `{2, 3}`)
  * `prog6_x9`:  6 input accesses, computing `382500000 * x^9`            (bad primes `{2, 3, 5, 17}`)
  * `prog7_x11`: 7 input accesses, computing `68724637549388656012800 * x^11`
  * `prog8_x13`: 8 input accesses, computing `2656207148788801777680 * x^13`
  * `prog9_x15`: 9 input accesses, computing `876702103804656272895371895753963647960420947968000 * x^15`

Each integer program executes cleanly over **EVERY commutative ring `R`**, restoring work
registers `(u, v)` identically and adding `D * x^N` to the passive output register `O`.
Over any ring/field `R` in which `D` has a multiplicative inverse (in particular `ℚ`, `ℝ`, `ℂ`,
and `𝔽_p` avoiding the explicit finite set of bad primes), scaling `addOut` coefficients by `D⁻¹`
yields exact monic programs proving:
  * `x^7  ∈ RP^{pass}_K(3, 5)`  (`log_7  5 ≈ 0.827087`),
  * `x^9  ∈ RP^{pass}_K(3, 6)`  (`log_9  6 ≈ 0.815465`),
  * `x^11 ∈ RP^{pass}_K(3, 7)`  (`log_11 7 ≈ 0.811508`),
  * `x^13 ∈ RP^{pass}_K(3, 8)`  (`log_13 8 ≈ 0.810714`, the unique integer minimum of `log_{2t-3} t`),
  * `x^15 ∈ RP^{pass}_K(3, 9)`  (`log_15 9 ≈ 0.811368`, post-minimum ascent point).

We also formally certify the entire strictly decreasing exponent chain via exact `Nat`
power inequalities with rational separators (`30/37`, `13/16`, `9/11`, `5/6`).
-/

namespace Catalytic

@[expose] public section

universe u

/-! ## 1. Literal 3-Register Passive-Output Register Program Model (Vinciguerra Def. 2.2) -/

/--
A primitive instruction of a passive-output 3-register program over registers `(O, u, v)`
with coefficients in a ring `R`:
  * `addOut p`:   `O ← O + ∑_{(a, b, c) ∈ p} c * u^a * v^b`  (basic op, passive output, 0 accesses)
  * `addWorkV c d`: `v ← v + c * u^d`                        (basic op, reads only `u`, 0 accesses)
  * `addInputU α`:  `u ← u + α * x`                          (input access: **1 access to `x`**)
-/
inductive Pass3InstrR (R : Type u) where
  | addOut (terms : List (Nat × Nat × R)) : Pass3InstrR R
  | addWorkV (coeff : R) (deg : Nat) : Pass3InstrR R
  | addInputU (alpha : R) : Pass3InstrR R

/-- Integer-coefficient 3-register passive program instruction. -/
abbrev Pass3Instr := Pass3InstrR Int

/-- Count input accesses in a 3-register passive program. -/
def Pass3Prog.accesses {R : Type u} : List (Pass3InstrR R) → Nat
  | [] => 0
  | .addOut _ :: rest => Pass3Prog.accesses rest
  | .addWorkV _ _ :: rest => Pass3Prog.accesses rest
  | .addInputU _ :: rest => 1 + Pass3Prog.accesses rest

/-- Evaluate a bivariate polynomial `∑ (a, b, c) => c * u^a * v^b` in any `CRing R`. -/
def evalBivar {R : Type u} [CRing R] (u v : R) : List (Nat × Nat × R) → R
  | [] => 0
  | (a, b, c) :: rest => c * (CRing.pow u a * CRing.pow v b) + evalBivar u v rest

/-- Execute one 3-register instruction over any `CRing R`. -/
def Pass3InstrR.exec {R : Type u} [CRing R] (x : R) (st : R × R × R) :
    Pass3InstrR R → R × R × R
  | .addOut terms => (st.1 + evalBivar st.2.1 st.2.2 terms, st.2.1, st.2.2)
  | .addWorkV c d => (st.1, st.2.1, st.2.2 + c * CRing.pow st.2.1 d)
  | .addInputU α => (st.1, st.2.1 + α * x, st.2.2)

/-- Execute a 3-register program left-to-right over any `CRing R`. -/
def Pass3Prog.exec {R : Type u} [CRing R] (x : R) :
    List (Pass3InstrR R) → (R × R × R) → (R × R × R)
  | [], st => st
  | i :: rest, st => Pass3Prog.exec x rest (i.exec x st)

/-- Cast an integer 3-register program into any `CRing R`, scaling output updates by `s : R`. -/
def Pass3Instr.scaleOut {R : Type u} [CRing R] (s : R) : Pass3Instr → Pass3InstrR R
  | .addOut terms => .addOut (terms.map fun (a, b, c) => (a, b, s * CRing.intCast c))
  | .addWorkV c d => .addWorkV (CRing.intCast c) d
  | .addInputU α => .addInputU (CRing.intCast α)

def Pass3Prog.scaleOut {R : Type u} [CRing R] (s : R) (p : List Pass3Instr) :
    List (Pass3InstrR R) :=
  p.map (Pass3Instr.scaleOut s)

theorem Pass3Prog.scaleOut_accesses {R : Type u} [CRing R] (s : R) (p : List Pass3Instr) :
    Pass3Prog.accesses (Pass3Prog.scaleOut s p) = Pass3Prog.accesses p := by
  induction p with
  | nil => rfl
  | cons i rest ih =>
    cases i <;>
      exact (by
        change Pass3Prog.accesses (Pass3Instr.scaleOut s _ :: Pass3Prog.scaleOut s rest) = _
        simp only [Pass3Instr.scaleOut, Pass3Prog.accesses, ih])

private theorem evalBivar_scale {R : Type u} [CRing R] (s u v : R)
    (terms : List (Nat × Nat × Int)) :
    evalBivar u v (terms.map fun (a, b, c) => (a, b, s * CRing.intCast c)) =
      s * evalBivar u v (terms.map fun (a, b, c) => (a, b, CRing.intCast c)) := by
  induction terms with
  | nil => simp [evalBivar]
  | cons hd tl ih =>
    rcases hd with ⟨a, b, c⟩
    simp only [List.map, evalBivar, ih, CRing.left_distrib, CRing.mul_assoc]

/-- Scaling all `addOut` instructions by `s : R` leaves `(u, v)` unchanged and scales `ΔO` by `s`. -/
theorem Pass3Prog.exec_scaleOut {R : Type u} [CRing R] (s x o o' u v : R) (p : List Pass3Instr) :
    let res1 := Pass3Prog.exec x (Pass3Prog.scaleOut (1 : R) p) (o, u, v)
    let resS := Pass3Prog.exec x (Pass3Prog.scaleOut s p) (o', u, v)
    resS.2 = res1.2 ∧
    ∀ Δ : R, res1.1 = o + Δ → resS.1 = o' + s * Δ := by
  induction p generalizing o o' u v with
  | nil =>
    refine ⟨rfl, ?_⟩
    intro Δ hΔ
    change o = o + Δ at hΔ
    have h0 : Δ = 0 := by
      have := CRing.add_left_cancel (a := o) (b := 0) (c := Δ) (by rw [CRing.add_zero]; exact hΔ)
      exact this.symm
    change o' = o' + s * Δ
    rw [h0, CRing.mul_zero, CRing.add_zero]
  | cons instr rest ih =>
    cases instr with
    | addOut terms =>
      change let res1 := Pass3Prog.exec x (Pass3Prog.scaleOut (1 : R) rest)
               (o + evalBivar u v (terms.map fun (a, b, c) => (a, b, (1 : R) * CRing.intCast c)), u, v)
             let resS := Pass3Prog.exec x (Pass3Prog.scaleOut s rest)
               (o' + evalBivar u v (terms.map fun (a, b, c) => (a, b, s * CRing.intCast c)), u, v)
             resS.2 = res1.2 ∧ ∀ Δ : R, res1.1 = o + Δ → resS.1 = o' + s * Δ
      let raw := evalBivar u v (terms.map fun (a, b, c) => (a, b, CRing.intCast c))
      have h1 : evalBivar u v (terms.map fun (a, b, c) => (a, b, (1 : R) * CRing.intCast c)) = raw := by
        rw [evalBivar_scale, CRing.one_mul]
      have hS : evalBivar u v (terms.map fun (a, b, c) => (a, b, s * CRing.intCast c)) = s * raw :=
        evalBivar_scale s u v terms
      rw [h1, hS]
      have hrec := ih (o + raw) (o' + s * raw) u v
      refine ⟨hrec.1, ?_⟩
      intro Δ hΔ
      have hΔ' : (Pass3Prog.exec x (Pass3Prog.scaleOut (1 : R) rest) (o + raw, u, v)).1 =
          (o + raw) + (Δ + -raw) := by
        rw [hΔ]
        calc
          o + Δ = o + (0 + Δ) := by rw [CRing.zero_add]
          _     = o + ((raw + -raw) + Δ) := by rw [CRing.add_neg]
          _     = o + (raw + (Δ + -raw)) := by rw [CRing.add_assoc, CRing.add_comm (-raw) Δ]
          _     = (o + raw) + (Δ + -raw) := (CRing.add_assoc _ _ _).symm
      have hres := hrec.2 (Δ + -raw) hΔ'
      rw [hres, CRing.left_distrib, CRing.mul_neg]
      calc
        (o' + s * raw) + (s * Δ + -(s * raw))
            = o' + ((s * raw + -(s * raw)) + s * Δ) := by
              rw [CRing.add_assoc, CRing.add_comm (s * Δ) (-(s * raw)), ← CRing.add_assoc (s * raw)]
        _   = o' + (0 + s * Δ) := by rw [CRing.add_neg]
        _   = o' + s * Δ := by rw [CRing.zero_add]
    | addWorkV c d =>
      simp only [Pass3Prog.scaleOut, List.map, Pass3Instr.scaleOut, Pass3Prog.exec, Pass3InstrR.exec]
      exact ih o o' u (v + CRing.intCast c * CRing.pow u d)
    | addInputU α =>
      simp only [Pass3Prog.scaleOut, List.map, Pass3Instr.scaleOut, Pass3Prog.exec, Pass3InstrR.exec]
      exact ih o o' (u + CRing.intCast α * x) v

/-! ## 2. Verified Sparse Trivariate Integer Polynomial Reducer (Pure Kernel Sound Reflection) -/

/-- Monomial exponent triple `(deg_x, deg_u, deg_v)`. -/
abbrev Mon3 := Nat × Nat × Nat

/-- Lexicographic strict ordering on `Mon3`. -/
def Mon3.lt (a b : Mon3) : Bool :=
  if a.1 != b.1 then a.1 < b.1
  else if a.2.1 != b.2.1 then a.2.1 < b.2.1
  else a.2.2 < b.2.2

/-- Sparse trivariate integer polynomial in `(x, u, v)`. -/
abbrev Poly3 := List (Mon3 × Int)

/-- Evaluate a `Poly3` in any commutative ring `R`. -/
def Poly3.eval {R : Type u} [CRing R] (x u v : R) : Poly3 → R
  | [] => 0
  | ((dx, du, dv), c) :: rest =>
    CRing.intCast c * (CRing.pow x dx * (CRing.pow u du * CRing.pow v dv)) + Poly3.eval x u v rest

/-- Structurally recursive merge-add of two sorted sparse polynomials (instant kernel reduction!). -/
def Poly3.addAux (m1 : Mon3) (c1 : Int) (addR1 : Poly3 → Poly3) : Poly3 → Poly3
  | [] => (m1, c1) :: addR1 []
  | (m2, c2) :: r2 =>
    if m1 == m2 then
      let c := c1 + c2
      if c == 0 then addR1 r2
      else (m1, c) :: addR1 r2
    else if Mon3.lt m1 m2 then
      (m1, c1) :: addR1 ((m2, c2) :: r2)
    else
      (m2, c2) :: Poly3.addAux m1 c1 addR1 r2

def Poly3.add : Poly3 → Poly3 → Poly3
  | [], q => q
  | (m1, c1) :: r1, q => Poly3.addAux m1 c1 (Poly3.add r1) q

/-- Scale a `Poly3` by an integer scalar `k`. -/
def Poly3.scale (k : Int) (p : Poly3) : Poly3 :=
  if k == 0 then []
  else p.map fun (m, c) => (m, k * c)

/-- Multiply a `Poly3` by a single term `(m, c)`. -/
def Poly3.mulTerm (m : Mon3) (c : Int) (p : Poly3) : Poly3 :=
  if c == 0 then []
  else p.map fun (m', c') => ((m.1 + m'.1, m.2.1 + m'.2.1, m.2.2 + m'.2.2), c * c')

/-- Multiply two `Poly3` polynomials using merge-addition. -/
def Poly3.mul : Poly3 → Poly3 → Poly3
  | [], _ => []
  | (m, c) :: rest, q => Poly3.add (Poly3.mulTerm m c q) (Poly3.mul rest q)

/-- Raise a `Poly3` to a natural-number power. -/
def Poly3.pow (p : Poly3) : Nat → Poly3
  | 0 => [((0, 0, 0), 1)]
  | n + 1 => Poly3.mul (Poly3.pow p n) p

private theorem Poly3.eval_addAux {R : Type u} [CRing R] (x u v : R)
    (m1 : Mon3) (c1 : Int) (r1 : Poly3) (addR1 : Poly3 → Poly3)
    (hadd : ∀ q, Poly3.eval x u v (addR1 q) = Poly3.eval x u v r1 + Poly3.eval x u v q)
    (q : Poly3) :
    Poly3.eval x u v (Poly3.addAux m1 c1 addR1 q) =
      (CRing.intCast c1 * (CRing.pow x m1.1 * (CRing.pow u m1.2.1 * CRing.pow v m1.2.2)) +
        Poly3.eval x u v r1) + Poly3.eval x u v q := by
  induction q with
  | nil =>
    rcases m1 with ⟨dx1, du1, dv1⟩
    simp only [Poly3.addAux, Poly3.eval, hadd [], CRing.add_zero]
  | cons t2 r2 ih2 =>
    rcases m1 with ⟨dx1, du1, dv1⟩
    rcases t2 with ⟨⟨dx2, du2, dv2⟩, c2⟩
    simp only [Poly3.addAux]
    split
    · rename_i heq
      have hmeq : (dx1, du1, dv1) = (dx2, du2, dv2) := beq_iff_eq.mp heq
      cases hmeq
      split
      · rename_i hc0
        have hc : c1 + c2 = 0 := beq_iff_eq.mp hc0
        rw [hadd r2]
        simp only [Poly3.eval]
        let M := CRing.pow x dx1 * (CRing.pow u du1 * CRing.pow v dv1)
        have hsum : (CRing.intCast c1 : R) * M + (CRing.intCast c2 : R) * M = 0 := by
          rw [← CRing.right_distrib, ← CRing.intCast_add, hc, CRing.intCast_zero, CRing.zero_mul]
        calc
          Poly3.eval x u v r1 + Poly3.eval x u v r2
              = 0 + (Poly3.eval x u v r1 + Poly3.eval x u v r2) := (CRing.zero_add _).symm
          _   = ((CRing.intCast c1 * M + CRing.intCast c2 * M) +
                 (Poly3.eval x u v r1 + Poly3.eval x u v r2)) := by rw [hsum]
          _   = (CRing.intCast c1 * M + Poly3.eval x u v r1) +
                (CRing.intCast c2 * M + Poly3.eval x u v r2) := by
                  rw [CRing.add_assoc, ← CRing.add_assoc (CRing.intCast c2 * M),
                      CRing.add_comm (CRing.intCast c2 * M) (Poly3.eval x u v r1),
                      CRing.add_assoc (Poly3.eval x u v r1), ← CRing.add_assoc]
      · rw [Poly3.eval, hadd r2, CRing.intCast_add, CRing.right_distrib]
        simp only [Poly3.eval]
        let A := CRing.intCast c1 * (CRing.pow x dx1 * (CRing.pow u du1 * CRing.pow v dv1))
        let B := CRing.intCast c2 * (CRing.pow x dx1 * (CRing.pow u du1 * CRing.pow v dv1))
        let E1 := Poly3.eval x u v r1
        let E2 := Poly3.eval x u v r2
        change (A + B) + (E1 + E2) = (A + E1) + (B + E2)
        rw [CRing.add_assoc, ← CRing.add_assoc B E1 E2, CRing.add_comm B E1,
            CRing.add_assoc E1 B E2, ← CRing.add_assoc]
    · split
      · rw [Poly3.eval, hadd (((dx2, du2, dv2), c2) :: r2)]
        simp only [Poly3.eval, CRing.add_assoc]
      · rw [Poly3.eval, ih2]
        simp only [Poly3.eval]
        let A := CRing.intCast c1 * (CRing.pow x dx1 * (CRing.pow u du1 * CRing.pow v dv1))
        let B := CRing.intCast c2 * (CRing.pow x dx2 * (CRing.pow u du2 * CRing.pow v dv2))
        let E1 := Poly3.eval x u v r1
        let E2 := Poly3.eval x u v r2
        change B + ((A + E1) + E2) = (A + E1) + (B + E2)
        rw [← CRing.add_assoc, CRing.add_comm B (A + E1), CRing.add_assoc]

theorem Poly3.eval_add {R : Type u} [CRing R] (x u v : R) (p q : Poly3) :
    Poly3.eval x u v (Poly3.add p q) = Poly3.eval x u v p + Poly3.eval x u v q := by
  induction p generalizing q with
  | nil => simp [Poly3.add, Poly3.eval, CRing.zero_add]
  | cons t1 r1 ih1 =>
    rcases t1 with ⟨m1, c1⟩
    simp only [Poly3.add, Poly3.eval]
    exact Poly3.eval_addAux x u v m1 c1 r1 (Poly3.add r1) ih1 q

theorem Poly3.eval_scale {R : Type u} [CRing R] (x u v : R) (k : Int) (p : Poly3) :
    Poly3.eval x u v (Poly3.scale k p) = CRing.intCast k * Poly3.eval x u v p := by
  simp only [Poly3.scale]
  split
  · rename_i hk0
    have hk : k = 0 := beq_iff_eq.mp hk0
    subst hk; simp [Poly3.eval]
  · induction p with
    | nil => simp [Poly3.eval]
    | cons hd tl ih =>
      rcases hd with ⟨⟨dx, du, dv⟩, c⟩
      simp only [List.map, Poly3.eval, ih, CRing.intCast_mul, CRing.left_distrib, CRing.mul_assoc]

theorem Poly3.eval_mulTerm {R : Type u} [CRing R] (x u v : R) (m : Mon3) (c : Int) (p : Poly3) :
    Poly3.eval x u v (Poly3.mulTerm m c p) =
      CRing.intCast c * (CRing.pow x m.1 * (CRing.pow u m.2.1 * CRing.pow v m.2.2)) *
        Poly3.eval x u v p := by
  simp only [Poly3.mulTerm]
  split
  · rename_i hc0
    have hc : c = 0 := beq_iff_eq.mp hc0
    subst hc; simp [Poly3.eval]
  · induction p with
    | nil => simp [Poly3.eval]
    | cons hd tl ih =>
      rcases hd with ⟨⟨dx, du, dv⟩, c'⟩
      simp only [List.map, Poly3.eval, ih, CRing.intCast_mul, CRing.pow_add, CRing.left_distrib]
      congr 1
      let C1 : R := CRing.intCast c
      let C2 : R := CRing.intCast c'
      let X1 := CRing.pow x m.1; let X2 := CRing.pow x dx
      let U1 := CRing.pow u m.2.1; let U2 := CRing.pow u du
      let V1 := CRing.pow v m.2.2; let V2 := CRing.pow v dv
      change (C1 * C2) * ((X1 * X2) * ((U1 * U2) * (V1 * V2))) =
        C1 * (X1 * (U1 * V1)) * (C2 * (X2 * (U2 * V2)))
      have hUV : (U1 * U2) * (V1 * V2) = (U1 * V1) * (U2 * V2) := by
        rw [CRing.mul_assoc, ← CRing.mul_assoc U2 V1 V2, CRing.mul_comm U2 V1,
            CRing.mul_assoc V1 U2 V2, ← CRing.mul_assoc]
      have hXUV : (X1 * X2) * ((U1 * V1) * (U2 * V2)) = (X1 * (U1 * V1)) * (X2 * (U2 * V2)) := by
        rw [CRing.mul_assoc, ← CRing.mul_assoc X2 (U1 * V1), CRing.mul_comm X2 (U1 * V1),
            CRing.mul_assoc (U1 * V1) X2, ← CRing.mul_assoc]
      rw [hUV, hXUV]
      rw [CRing.mul_assoc, ← CRing.mul_assoc C2 (X1 * (U1 * V1)), CRing.mul_comm C2 (X1 * (U1 * V1)),
          CRing.mul_assoc (X1 * (U1 * V1)) C2, ← CRing.mul_assoc]

theorem Poly3.eval_mul {R : Type u} [CRing R] (x u v : R) (p q : Poly3) :
    Poly3.eval x u v (Poly3.mul p q) = Poly3.eval x u v p * Poly3.eval x u v q := by
  induction p with
  | nil => simp [Poly3.mul, Poly3.eval]
  | cons hd tl ih =>
    rcases hd with ⟨⟨dx, du, dv⟩, c⟩
    simp only [Poly3.mul, Poly3.eval_add, Poly3.eval_mulTerm, ih, Poly3.eval, CRing.right_distrib]

theorem Poly3.eval_pow {R : Type u} [CRing R] (x u v : R) (p : Poly3) (n : Nat) :
    Poly3.eval x u v (Poly3.pow p n) = CRing.pow (Poly3.eval x u v p) n := by
  induction n with
  | zero => simp [Poly3.pow, Poly3.eval]
  | succ k ih =>
    simp only [Poly3.pow, Poly3.eval_mul, ih, CRing.pow]

/-- Symbolic evaluation of a bivariate output polynomial at `(pu, pv)`. -/
def evalBivarPoly (pu pv : Poly3) : List (Nat × Nat × Int) → Poly3
  | [] => []
  | (a, b, c) :: rest =>
    Poly3.add (Poly3.scale c (Poly3.mul (Poly3.pow pu a) (Poly3.pow pv b)))
      (evalBivarPoly pu pv rest)

theorem evalBivarPoly_sound {R : Type u} [CRing R] (x u v : R)
    (pu pv : Poly3) (terms : List (Nat × Nat × Int)) :
    Poly3.eval x u v (evalBivarPoly pu pv terms) =
      evalBivar (Poly3.eval x u v pu) (Poly3.eval x u v pv)
        (terms.map fun (a, b, c) => (a, b, (1 : R) * CRing.intCast c)) := by
  induction terms with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨a, b, c⟩
    simp only [evalBivarPoly, List.map, evalBivar, Poly3.eval_add, Poly3.eval_scale,
      Poly3.eval_mul, Poly3.eval_pow, ih, CRing.one_mul]

/-- Symbolic execution of an integer 3-register program over `Poly3`. -/
def exec3PolyAux : List Pass3Instr → Poly3 × Poly3 × Poly3 → Poly3 × Poly3 × Poly3
  | [], st => st
  | .addOut terms :: rest, (po, pu, pv) =>
    exec3PolyAux rest (Poly3.add po (evalBivarPoly pu pv terms), pu, pv)
  | .addWorkV c d :: rest, (po, pu, pv) =>
    exec3PolyAux rest (po, pu, Poly3.add pv (Poly3.scale c (Poly3.pow pu d)))
  | .addInputU α :: rest, (po, pu, pv) =>
    exec3PolyAux rest (po, Poly3.add pu (Poly3.scale α [((1, 0, 0), 1)]), pv)

def exec3Poly (p : List Pass3Instr) : Poly3 × Poly3 × Poly3 :=
  exec3PolyAux p ([], [((0, 1, 0), 1)], [((0, 0, 1), 1)])

private theorem exec3PolyAux_sound {R : Type u} [CRing R] (x o u v : R)
    (p : List Pass3Instr) (po pu pv : Poly3) :
    Pass3Prog.exec x (Pass3Prog.scaleOut (1 : R) p)
      (o + Poly3.eval x u v po, Poly3.eval x u v pu, Poly3.eval x u v pv) =
      let res := exec3PolyAux p (po, pu, pv)
      (o + Poly3.eval x u v res.1, Poly3.eval x u v res.2.1, Poly3.eval x u v res.2.2) := by
  induction p generalizing po pu pv with
  | nil => rfl
  | cons instr rest ih =>
    cases instr with
    | addOut terms =>
      simp only [Pass3Prog.scaleOut, List.map, Pass3Instr.scaleOut, Pass3Prog.exec,
        Pass3InstrR.exec, exec3PolyAux]
      have h1 : o + Poly3.eval x u v po +
          evalBivar (Poly3.eval x u v pu) (Poly3.eval x u v pv)
            (terms.map fun (a, b, c) => (a, b, (1 : R) * CRing.intCast c)) =
          o + Poly3.eval x u v (Poly3.add po (evalBivarPoly pu pv terms)) := by
        rw [Poly3.eval_add, evalBivarPoly_sound, CRing.add_assoc]
      rw [h1]
      exact ih (Poly3.add po (evalBivarPoly pu pv terms)) pu pv
    | addWorkV c d =>
      simp only [Pass3Prog.scaleOut, List.map, Pass3Instr.scaleOut, Pass3Prog.exec,
        Pass3InstrR.exec, exec3PolyAux]
      have h1 : Poly3.eval x u v pv + CRing.intCast c * CRing.pow (Poly3.eval x u v pu) d =
          Poly3.eval x u v (Poly3.add pv (Poly3.scale c (Poly3.pow pu d))) := by
        rw [Poly3.eval_add, Poly3.eval_scale, Poly3.eval_pow]
      rw [h1]
      exact ih po pu (Poly3.add pv (Poly3.scale c (Poly3.pow pu d)))
    | addInputU α =>
      simp only [Pass3Prog.scaleOut, List.map, Pass3Instr.scaleOut, Pass3Prog.exec,
        Pass3InstrR.exec, exec3PolyAux]
      have hx : Poly3.eval x u v (Poly3.scale α [((1, 0, 0), 1)]) = CRing.intCast α * x := by
        simp [Poly3.eval_scale, Poly3.eval, CRing.one_mul]
      have h1 : Poly3.eval x u v pu + CRing.intCast α * x =
          Poly3.eval x u v (Poly3.add pu (Poly3.scale α [((1, 0, 0), 1)])) := by
        rw [Poly3.eval_add, hx]
      rw [h1]
      exact ih po (Poly3.add pu (Poly3.scale α [((1, 0, 0), 1)])) pv

/--
Master soundness bridge: if `exec3Poly p = ([((N, 0, 0), D)], [((0, 1, 0), 1)], [((0, 0, 1), 1)])`,
then:
  1. Over EVERY commutative ring `R`, `Pass3Prog.scaleOut 1 p` cleanly computes `O ← O + D * x^N`.
  2. Over EVERY commutative ring `R` with an inverse `invD : R` (`invD * intCast D = 1`),
     `Pass3Prog.scaleOut invD p` cleanly computes `O ← O + x^N` with the exact same access count!
-/
theorem exec3Poly_certifies_monic {R : Type u} [CRing R]
    (p : List Pass3Instr) (N : Nat) (D : Int)
    (hcert : exec3Poly p = ([((N, 0, 0), D)], [((0, 1, 0), 1)], [((0, 0, 1), 1)]))
    (invD : R) (hinv : invD * CRing.intCast D = 1) (x o u v : R) :
    Pass3Prog.exec x (Pass3Prog.scaleOut invD p) (o, u, v) =
      (o + CRing.pow x N, u, v) := by
  have h1 := exec3PolyAux_sound (R := R) x o u v p [] [((0, 1, 0), 1)] [((0, 0, 1), 1)]
  have he0 : Poly3.eval x u v [] = (0 : R) := rfl
  have heu : Poly3.eval x u v [((0, 1, 0), 1)] = u := by
    simp [Poly3.eval, CRing.one_mul]
  have hev : Poly3.eval x u v [((0, 0, 1), 1)] = v := by
    simp [Poly3.eval, CRing.one_mul]
  rw [he0, heu, hev, CRing.add_zero] at h1
  change Pass3Prog.exec x (Pass3Prog.scaleOut (1 : R) p) (o, u, v) =
    let res := exec3Poly p
    (o + Poly3.eval x u v res.1, Poly3.eval x u v res.2.1, Poly3.eval x u v res.2.2) at h1
  rw [hcert] at h1
  simp only [Poly3.eval, CRing.pow_zero, CRing.pow_one, CRing.mul_one, CRing.add_zero,
    CRing.intCast_one, CRing.one_mul] at h1
  have hscale := Pass3Prog.exec_scaleOut (R := R) invD x o o u v p
  have h2 := hscale.1
  have h3 := hscale.2 (CRing.intCast D * CRing.pow x N) (by rw [h1])
  rw [h1] at h2
  have hprod : invD * (CRing.intCast D * CRing.pow x N) = CRing.pow x N := by
    rw [← CRing.mul_assoc, hinv, CRing.one_mul]
  rw [hprod] at h3
  exact Prod.ext h3 h2

/-! ## 3. The Five Explicit Improvement Programs (`t = 5, 6, 7, 8, 9`) -/

/-- Helper building one loop iteration `(addOut F) -> (v -= q*u^d) -> (u += α*x) -> (v += q*u^d)`. -/
def loopStep (d : Nat) (F : List (Nat × Nat × Int)) (q_next alpha : Int) : List Pass3Instr :=
  [.addOut F] ++
  (if q_next == 0 then [] else [.addWorkV (-q_next) d]) ++
  [.addInputU alpha] ++
  (if q_next == 0 then [] else [.addWorkV q_next d])

/-- **Program 5 (`t = 5` accesses, `d = 2`, `N = 7`, `D = 576`, bad primes ONLY `{2, 3}`!).** -/
def prog5_x7 : List Pass3Instr :=
  loopStep 2 [(7, 0, -1567), (5, 1, -5292), (3, 2, -7245), (1, 3, -3570)] (-1) 1 ++
  loopStep 2 [(7, 0, -73006), (5, 1, 92358), (3, 2, -29610), (1, 3, 9730)] 3 1 ++
  loopStep 2 [(5, 1, -174132), (1, 3, -12320)] (-3) 1 ++
  loopStep 2 [(7, 0, 73006), (5, 1, 92358), (3, 2, 29610), (1, 3, 9730)] 1 1 ++
  loopStep 2 [(7, 0, 1567), (5, 1, -5292), (3, 2, 7245), (1, 3, -3570)] 0 (-4)

/-- **Program 6 (`t = 6` accesses, `d = 4`, `N = 9`, `D = 382500000`, bad primes `{2, 3, 5, 17}`).** -/
def prog6_x9 : List Pass3Instr :=
  loopStep 4 [(9, 0, 4154985), (5, 1, -9394056), (1, 2, 5454540)] 1 1 ++
  loopStep 4 [(9, 0, -72618275), (5, 1, -30013200), (1, 2, -12729150)] (-4) 1 ++
  loopStep 4 [(9, 0, 193081500), (5, 1, -8505000), (1, 2, 10914750)] 6 1 ++
  loopStep 4 [(9, 0, -193081500), (5, 1, 8505000), (1, 2, -10914750)] (-4) 1 ++
  loopStep 4 [(9, 0, 72618275), (5, 1, 30013200), (1, 2, 12729150)] 1 1 ++
  loopStep 4 [(9, 0, -4154985), (5, 1, 9394056), (1, 2, -5454540)] 0 (-5)

/-- **Program 7 (`t = 7` accesses, `d = 5`, `N = 11`, `D = 68724637549388656012800`).** -/
def prog7_x11 : List Pass3Instr :=
  loopStep 5 [(11, 0, 7906012563161999776548), (6, 1, 2913565459167362672640), (1, 2, 359752416281925314670)] (-6) 1 ++
  loopStep 5 [(11, 0, -160487039610242232432475), (6, 1, 9002890386212446808700), (1, 2, -575226836894382807750)] 29 1 ++
  loopStep 5 [(11, 0, 739254464056809087842322), (6, 1, 11855322660827313965220), (1, 2, 491370792119074417242)] (-55) 1 ++
  loopStep 5 [(11, 0, -1074623435277851316121425), (6, 1, -2062222051271515088340), (1, 2, -523787405092533868902)] 50 1 ++
  loopStep 5 [(11, 0, 563164798398494126351300), (6, 1, -13184058990777727982160), (1, 2, 509164691003954780718)] (-20) 1 ++
  loopStep 5 [(11, 0, -75339810861908276105898), (6, 1, -8247961873263806201970), (1, 2, -478052152922140654473)] 1 2 ++
  loopStep 5 [(11, 0, 125010731536610689628), (6, 1, -277535590894074174090), (1, 2, 216778495504102818495)] 0 (-7)

/-- **Program 8 (`t = 8` accesses, `d = 6`, `N = 13`, `D = 2656207148788801777680` — optimal exponent!).** -/
def prog8_x13 : List Pass3Instr :=
  loopStep 6 [(13, 0, 48815710996788904), (7, 1, -106093571331033000), (1, 2, 60350317640973360)] 1 1 ++
  loopStep 6 [(13, 0, -1658292324977727901), (7, 1, -489368519245585980), (1, 2, -127682705470680360)] (-6) 1 ++
  loopStep 6 [(13, 0, 10834057724039418729), (7, 1, -755802943366571100), (1, 2, 109443420226524384)] 15 1 ++
  loopStep 6 [(13, 0, -28066770107640654530), (7, 1, -709685716297357800), (1, 2, -112368956812984872)] (-20) 1 ++
  loopStep 6 [(13, 0, 28066770107640654530), (7, 1, 709685716297357800), (1, 2, 112368956812984872)] 15 1 ++
  loopStep 6 [(13, 0, -10834057724039418729), (7, 1, 755802943366571100), (1, 2, -109443420226524384)] (-6) 1 ++
  loopStep 6 [(13, 0, 1658292324977727901), (7, 1, 489368519245585980), (1, 2, 127682705470680360)] 1 1 ++
  loopStep 6 [(13, 0, -48815710996788904), (7, 1, 106093571331033000), (1, 2, -60350317640973360)] 0 (-7)

/-- 9-access, 3-register integer program computing `876702103804656272895371895753963647960420947968000 * x^15`
(`d = 7`, shifts `[0, 1, 2, 3, 4, 5, 6, 7, 9]`, exponent `log_15 9 ≈ 0.811368 > log_13 8`). -/
def prog9_x15 : List Pass3Instr :=
  loopStep 7 [(15, 0, 47697576695807591149970091225524143671006608128), (8, 1, 12828801617978706859373312286292362540907084800), (1, 2, 1110886294449659745864096749366203925109120600)] (-8) 1 ++
  loopStep 7 [(15, 0, -1869508609729587846176068147939982519944593238713), (8, 1, 59996502939059511159195477622864433675594894400), (1, 2, -1786938821946514648844378151300481931148403800)] 55 1 ++
  loopStep 7 [(15, 0, 18929285835903525682822071783431297700189705828150), (8, 1, 156868870192178246016753489647911722864476079660), (1, 2, 1554796487897524506238230241861352577945418230)] (-161) 1 ++
  loopStep 7 [(15, 0, -59701354430749272030885419618468843480279798575140), (8, 1, 126572346189002105604280213928792980703987534280), (1, 2, -1618444280603445010428031257340298209769887860)] 259 1 ++
  loopStep 7 [(15, 0, 80464114702764739278983389227647015096532834945642), (8, 1, -21050480064011964593421747180018455328448123740), (1, 2, 1539451953576780013877480778907171940215731930)] (-245) 1 ++
  loopStep 7 [(15, 0, -49538529867529484855836135637226966605728933525908), (8, 1, -145439140733739384863055551545682276887938764400), (1, 2, -1611646744675379323642096886402195841667682400)] 133 1 ++
  loopStep 7 [(15, 0, 12439625519035786199231464105054913816402633009958), (8, 1, -141436572689870378712533337515868209608737690300), (1, 2, 1613128695684116497614060659740636235214780150)] (-35) 1 ++
  loopStep 7 [(15, 0, -771759365416347953099835753244141156083904814775), (8, 1, -47414065101749587510890697899583576459910516250), (1, 2, -1482717341185777135391234005514321851922862975)] 1 2 ++
  loopStep 7 [(15, 0, 428639024833933810563949521183005241049762658), (8, 1, -926262348847253959701159344708981499930498450), (1, 2, 681483756803035354711871870681933156023786125)] 0 (-9)

theorem prog5_x7_accesses : Pass3Prog.accesses prog5_x7 = 5 := rfl
theorem prog6_x9_accesses : Pass3Prog.accesses prog6_x9 = 6 := rfl
theorem prog7_x11_accesses : Pass3Prog.accesses prog7_x11 = 7 := rfl
theorem prog8_x13_accesses : Pass3Prog.accesses prog8_x13 = 8 := rfl
theorem prog9_x15_accesses : Pass3Prog.accesses prog9_x15 = 9 := rfl

private theorem prog5_x7_cert :
    exec3Poly prog5_x7 = ([((7, 0, 0), 576)], [((0, 1, 0), 1)], [((0, 0, 1), 1)]) := rfl

private theorem prog6_x9_cert :
    exec3Poly prog6_x9 = ([((9, 0, 0), 382500000)], [((0, 1, 0), 1)], [((0, 0, 1), 1)]) := rfl

private theorem prog7_x11_cert :
    exec3Poly prog7_x11 =
      ([((11, 0, 0), 68724637549388656012800)], [((0, 1, 0), 1)], [((0, 0, 1), 1)]) := rfl

set_option maxRecDepth 4096 in
private theorem prog8_x13_cert :
    exec3Poly prog8_x13 =
      ([((13, 0, 0), 2656207148788801777680)], [((0, 1, 0), 1)], [((0, 0, 1), 1)]) := rfl

set_option maxRecDepth 8192 in
private theorem prog9_x15_cert :
    exec3Poly prog9_x15 =
      ([((15, 0, 0), 876702103804656272895371895753963647960420947968000)],
       [((0, 1, 0), 1)], [((0, 0, 1), 1)]) := rfl

/-- **Theorem T3a (`x^7 ∈ RP^{pass}_R(3, 5)` whenever `576` is invertible, i.e. `char ≠ 2, 3`).** -/
theorem three_reg_5call_x7 {R : Type u} [CRing R]
    (inv576 : R) (hinv : inv576 * CRing.intCast 576 = 1) :
    Pass3Prog.accesses (Pass3Prog.scaleOut inv576 prog5_x7) = 5 ∧
    ∀ x o u v : R,
      Pass3Prog.exec x (Pass3Prog.scaleOut inv576 prog5_x7) (o, u, v) = (o + CRing.pow x 7, u, v) :=
  ⟨by rw [Pass3Prog.scaleOut_accesses]; exact prog5_x7_accesses,
   fun x o u v => exec3Poly_certifies_monic prog5_x7 7 576 prog5_x7_cert inv576 hinv x o u v⟩

/-- **Theorem T3b (`x^9 ∈ RP^{pass}_R(3, 6)` whenever `382500000` is invertible, i.e. `char ∉ {2,3,5,17}`).** -/
theorem three_reg_6call_x9 {R : Type u} [CRing R]
    (invD : R) (hinv : invD * CRing.intCast 382500000 = 1) :
    Pass3Prog.accesses (Pass3Prog.scaleOut invD prog6_x9) = 6 ∧
    ∀ x o u v : R,
      Pass3Prog.exec x (Pass3Prog.scaleOut invD prog6_x9) (o, u, v) = (o + CRing.pow x 9, u, v) :=
  ⟨by rw [Pass3Prog.scaleOut_accesses]; exact prog6_x9_accesses,
   fun x o u v => exec3Poly_certifies_monic prog6_x9 9 382500000 prog6_x9_cert invD hinv x o u v⟩

/-- **Theorem T3c (`x^11 ∈ RP^{pass}_R(3, 7)` over `ℚ` and all good prime characteristics).** -/
theorem three_reg_7call_x11 {R : Type u} [CRing R]
    (invD : R) (hinv : invD * CRing.intCast 68724637549388656012800 = 1) :
    Pass3Prog.accesses (Pass3Prog.scaleOut invD prog7_x11) = 7 ∧
    ∀ x o u v : R,
      Pass3Prog.exec x (Pass3Prog.scaleOut invD prog7_x11) (o, u, v) = (o + CRing.pow x 11, u, v) :=
  ⟨by rw [Pass3Prog.scaleOut_accesses]; exact prog7_x11_accesses,
   fun x o u v =>
     exec3Poly_certifies_monic prog7_x11 11 68724637549388656012800 prog7_x11_cert invD hinv x o u v⟩

/-- **Theorem T3d (`x^13 ∈ RP^{pass}_R(3, 8)` — optimal 3-register exponent `log_13 8 ≈ 0.810714`).** -/
theorem three_reg_8call_x13 {R : Type u} [CRing R]
    (invD : R) (hinv : invD * CRing.intCast 2656207148788801777680 = 1) :
    Pass3Prog.accesses (Pass3Prog.scaleOut invD prog8_x13) = 8 ∧
    ∀ x o u v : R,
      Pass3Prog.exec x (Pass3Prog.scaleOut invD prog8_x13) (o, u, v) = (o + CRing.pow x 13, u, v) :=
  ⟨by rw [Pass3Prog.scaleOut_accesses]; exact prog8_x13_accesses,
   fun x o u v =>
     exec3Poly_certifies_monic prog8_x13 13 2656207148788801777680 prog8_x13_cert invD hinv x o u v⟩

/-- **Theorem T3g (`x^15 ∈ RP^{pass}_R(3, 9)` — post-minimum ascent point `log_15 9 ≈ 0.811368`).** -/
theorem three_reg_9call_x15 {R : Type u} [CRing R]
    (invD : R) (hinv : invD * CRing.intCast 876702103804656272895371895753963647960420947968000 = 1) :
    Pass3Prog.accesses (Pass3Prog.scaleOut invD prog9_x15) = 9 ∧
    ∀ x o u v : R,
      Pass3Prog.exec x (Pass3Prog.scaleOut invD prog9_x15) (o, u, v) = (o + CRing.pow x 15, u, v) :=
  ⟨by rw [Pass3Prog.scaleOut_accesses]; exact prog9_x15_accesses,
   fun x o u v =>
     exec3Poly_certifies_monic prog9_x15 15 876702103804656272895371895753963647960420947968000
       prog9_x15_cert invD hinv x o u v⟩

/-! ## 4. Exact Natural-Number Proof of the Strictly Decreasing Exponent Chain -/

/--
Exact rational separation proving:
  `log_13 8 < 30/37 < log_11 7 < 13/16 < log_9 6 < 9/11 < log_7 5 < 5/6 < log_5 4`
  and `log_13 8 < 30/37 < log_15 9`
using pure `Nat` exponentiation (`a^q < b^p ⇔ log_b a < p/q` for `a, b > 1`).
-/
theorem exponent_strict_improvement_chain :
    (8 ^ 37 < 13 ^ 30) ∧ (11 ^ 30 < 7 ^ 37) ∧
    (7 ^ 16 < 11 ^ 13) ∧ (9 ^ 13 < 6 ^ 16) ∧
    (6 ^ 11 < 9 ^ 9)   ∧ (7 ^ 9 < 5 ^ 11) ∧
    (5 ^ 6 < 7 ^ 5)    ∧ (5 ^ 5 < 4 ^ 6) ∧
    (15 ^ 30 < 9 ^ 37) := by
  decide

private theorem nat_pow_le_pow_left {a b : Nat} (h : a ≤ b) : ∀ n : Nat, a ^ n ≤ b ^ n
  | 0 => Nat.le_refl 1
  | n + 1 => by
    simp only [Nat.pow_succ]
    exact Nat.mul_le_mul (nat_pow_le_pow_left h n) h

private theorem nat_mul_pow (a b : Nat) : ∀ n : Nat, (a * b) ^ n = a ^ n * b ^ n
  | 0 => rfl
  | n + 1 => by
    simp only [Nat.pow_succ, nat_mul_pow a b n]
    calc
      a ^ n * b ^ n * (a * b) = a ^ n * (b ^ n * a * b) := by
        rw [Nat.mul_assoc, ← Nat.mul_assoc (b ^ n) a b]
      _ = a ^ n * (a * b ^ n * b) := by rw [Nat.mul_comm (b ^ n) a]
      _ = (a ^ n * a) * (b ^ n * b) := by rw [Nat.mul_assoc, Nat.mul_assoc]

/--
**Theorem T3f (Unconditional Global Integer Optimality of `t = 8` for All `t ≥ 4`):**
Certifies via the single rational separator `30 / 37` that
`log_13 8 < 30 / 37 < log_{2t - 3} t` for EVERY integer `t ≥ 4` with `t ≠ 8`:
  1. `8 ^ 37 < 13 ^ 30`, and
  2. `∀ t : Nat, 4 ≤ t → t ≠ 8 → (2 * t - 3) ^ 30 < t ^ 37`.
Proved in pure `Nat` arithmetic using only `[propext, Quot.sound]` (no `Classical.choice`).
-/
theorem exponent_global_integer_optimality :
    (8 ^ 37 < 13 ^ 30) ∧
    (∀ t : Nat, 4 ≤ t → t ≠ 8 → (2 * t - 3) ^ 30 < t ^ 37) := by
  refine ⟨by decide, ?_⟩
  intro t ht4 ht8
  by_cases hlt : t < 20
  · have hcases :
        t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 9 ∨ t = 10 ∨ t = 11 ∨ t = 12 ∨
        t = 13 ∨ t = 14 ∨ t = 15 ∨ t = 16 ∨ t = 17 ∨ t = 18 ∨ t = 19 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · have ht20 : 20 ≤ t := by omega
    have h1 : (2 * t - 3) ^ 30 ≤ (2 * t) ^ 30 := nat_pow_le_pow_left (by omega) 30
    have h2 : (2 * t) ^ 30 = 2 ^ 30 * t ^ 30 := nat_mul_pow 2 t 30
    have h3 : 2 ^ 30 < 20 ^ 7 := by decide
    have h4 : 20 ^ 7 ≤ t ^ 7 := nat_pow_le_pow_left ht20 7
    have h5 : 0 < t ^ 30 := Nat.pow_pos (by omega)
    have h6 : 2 ^ 30 * t ^ 30 < t ^ 7 * t ^ 30 :=
      Nat.mul_lt_mul_of_pos_right (Nat.lt_of_lt_of_le h3 h4) h5
    have h7 : t ^ 7 * t ^ 30 = t ^ 37 := (Nat.pow_add t 7 30).symm
    exact Nat.lt_of_le_of_lt h1 (by rw [h2, ← h7]; exact h6)

end

end Catalytic
