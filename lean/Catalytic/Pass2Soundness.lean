module
-- SPDX-License-Identifier: Apache-2.0

public import Catalytic.CommRing
public import Catalytic.PrimeFieldTools
public import Catalytic.DigitSumDichotomy
public import Catalytic.ExtensionFieldSeparation

/-!
# Literal Commutative-Ring Soundness Bridge for `T1` and `T1e`

In `Catalytic.DigitSumDichotomy` and `Catalytic.ExtensionFieldSeparation`, passive 2-register
programs (`Pass2Instr` over `𝔽_p` and `Pass2GF4Instr` over `𝔽_4`) are executed symbolically on
formal coefficient tables via `polyAtShiftCoeff` and `polyAtShiftCoeffGF4`.

To eliminate any formal-definition trust-base gap between symbolic binomial-coefficient execution
and literal ring evaluation, this module:
  1. Proves the **binomial theorem** `CRing.add_pow` from first principles over every commutative
     ring `R` (`[CRing R]`) with zero Mathlib dependencies.
  2. Defines direct literal ring execution `Pass2Prog.execRing` (literally `O ← O + evalPolyR poly r`,
     `r ← r + natCast c`, `O ← O + natCast lam * x`, `r ← r + natCast lam * x`) with NO binomial
     coefficients anywhere in its definition.
  3. Proves **Theorem `T1s_Pass2RingSoundness`** and **Theorem `T1sc_Pass2RingEquiv`**: for EVERY
     program `prog`, EVERY modulus `p > 1`, and EVERY polynomial `f`, symbolic `CleanlyComputes2 p prog f`
     holds **if and only if (`↔`)** literal ring execution `Pass2Prog.execRing` cleanly maps
     `(o, u) ↦ (o + evalPolyR f x, u)` over **every** characteristic-`p` commutative ring `R`
     (with completeness proved constructively via the formal power series ring `FPS (FPS (ModP p hp))`).
     This yields Theorem `T1` (`rp_pass_two_literal_ring_iff`) stated directly on literal ring execution.
  4. Defines direct literal execution `Pass2GF4Prog.execAlg` over ANY commutative `GF4`-algebra `R`
     (via any ring homomorphism `φ : GF4 → R`, including `R = GF4` with `φ = id`) and proves
     **Theorem `T1es_Pass2GF4Soundness`** and **Theorem `T1esc_Pass2GF4Equiv`**: symbolic
     `CleanlyComputes2GF4 prog f` holds **if and only if (`↔`)** literal `GF4`-algebra execution
     cleanly maps `(o, u) ↦ (o + evalPolyGF4Alg φ f x, u)` over every commutative `GF4`-algebra `(R, φ)`
     (with completeness proved via `FPS (FPS GF4)`).
-/

namespace Catalytic

@[expose] public section

universe u

/-! ## 1. Finite Ring Sums and the Zero-Mathlib Binomial Theorem -/

/-- Finite sum `f 0 + f 1 + ... + f (n - 1)` in an arbitrary commutative ring `R`. -/
def sumR {R : Type u} [CRing R] : Nat → (Nat → R) → R
  | 0, _     => 0
  | n + 1, f => sumR n f + f n

section RingSums

variable {R : Type u} [CRing R]

@[simp] theorem sumR_zero (f : Nat → R) : sumR 0 f = 0 := rfl

theorem sumR_succ (n : Nat) (f : Nat → R) : sumR (n + 1) f = sumR n f + f n := rfl

theorem sumR_congr {n : Nat} {f g : Nat → R} (h : ∀ i < n, f i = g i) :
    sumR n f = sumR n g := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [sumR_succ, sumR_succ, ih (fun i hi => h i (by omega)), h m (Nat.lt_succ_self m)]

theorem sumR_eq_zero {n : Nat} {f : Nat → R} (h : ∀ i < n, f i = 0) :
    sumR n f = 0 := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [sumR_succ, ih (fun i hi => h i (by omega)), h m (Nat.lt_succ_self m), CRing.add_zero]

theorem sumR_add (n : Nat) (f g : Nat → R) :
    sumR n (fun i => f i + g i) = sumR n f + sumR n g := by
  induction n with
  | zero => simp [sumR]
  | succ m ih =>
    rw [sumR_succ, sumR_succ, sumR_succ, ih]
    calc
      (sumR m f + sumR m g) + (f m + g m)
          = sumR m f + (sumR m g + (f m + g m)) := CRing.add_assoc _ _ _
      _   = sumR m f + ((sumR m g + f m) + g m) := by rw [← CRing.add_assoc (sumR m g)]
      _   = sumR m f + ((f m + sumR m g) + g m) := by rw [CRing.add_comm (sumR m g) (f m)]
      _   = sumR m f + (f m + (sumR m g + g m)) := by rw [CRing.add_assoc (f m)]
      _   = (sumR m f + f m) + (sumR m g + g m) := (CRing.add_assoc _ _ _).symm

theorem sumR_mul_left (n : Nat) (c : R) (f : Nat → R) :
    sumR n (fun i => c * f i) = c * sumR n f := by
  induction n with
  | zero => simp [sumR]
  | succ m ih =>
    rw [sumR_succ, sumR_succ, ih, CRing.left_distrib]

theorem sumR_mul_right (n : Nat) (f : Nat → R) (c : R) :
    sumR n (fun i => f i * c) = sumR n f * c := by
  induction n with
  | zero => simp [sumR]
  | succ m ih =>
    rw [sumR_succ, sumR_succ, ih, CRing.right_distrib]

theorem sumR_swap (m n : Nat) (f : Nat → Nat → R) :
    sumR m (fun i => sumR n (fun j => f i j)) =
      sumR n (fun j => sumR m (fun i => f i j)) := by
  induction m with
  | zero =>
    symm
    exact sumR_eq_zero (fun _ _ => rfl)
  | succ m' ih =>
    rw [sumR_succ, ih]
    symm
    exact sumR_add n (fun j => sumR m' (fun i => f i j)) (fun j => f m' j)

theorem sumR_succ_shift (n : Nat) (f : Nat → R) :
    sumR (n + 1) f = f 0 + sumR n (fun i => f (i + 1)) := by
  induction n with
  | zero => simp [sumR, CRing.zero_add]
  | succ m ih =>
    rw [sumR_succ, ih, sumR_succ, CRing.add_assoc]

theorem sumR_extend {m n : Nat} (hmn : m ≤ n) {f : Nat → R}
    (hz : ∀ i, m ≤ i → i < n → f i = 0) :
    sumR m f = sumR n f := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  induction k with
  | zero => simp
  | succ k' ih =>
    have hprev : sumR m f = sumR (m + k') f :=
      ih (by omega) (fun i hi1 hi2 => hz i hi1 (by omega))
    have hlast : f (m + k') = 0 := hz (m + k') (by omega) (by omega)
    have hstep : m + (k' + 1) = (m + k') + 1 := by omega
    rw [hstep, sumR_succ, ← hprev, hlast, CRing.add_zero]

theorem sumR_single {n j : Nat} (hj : j < n) (v : R) :
    sumR n (fun i => if i = j then v else 0) = v := by
  induction n with
  | zero => omega
  | succ m ih =>
    rw [sumR_succ]
    by_cases hjm : j = m
    · subst hjm
      have hzero : sumR j (fun i => if i = j then v else 0) = 0 :=
        sumR_eq_zero (fun i hi => by
          have hne : i ≠ j := by omega
          simp only [hne, ↓reduceIte])
      rw [hzero, CRing.zero_add]
      simp only [↓reduceIte]
    · have hjlt : j < m := by omega
      have hne : m ≠ j := by omega
      rw [ih hjlt]
      simp only [hne, ↓reduceIte, CRing.add_zero]

theorem natCast_sumNat (n : Nat) (f : Nat → Nat) :
    (CRing.natCast (sumNat n f) : R) = sumR n (fun i => CRing.natCast (f i)) := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [sumNat_succ, CRing.natCast_add, ih, sumR_succ]

theorem natCast_pow (a k : Nat) :
    (CRing.natCast (a ^ k) : R) = CRing.pow (CRing.natCast a) k := by
  induction k with
  | zero => simp [CRing.pow]
  | succ m ih =>
    rw [Nat.pow_succ, CRing.natCast_mul, ih, CRing.pow]

theorem natCast_mod_eq {p : Nat} (hchar : (CRing.natCast p : R) = 0) (n : Nat) :
    (CRing.natCast (n % p) : R) = CRing.natCast n := by
  have hdiv : n = p * (n / p) + n % p := (Nat.div_add_mod n p).symm
  conv => rhs; rw [hdiv]
  rw [CRing.natCast_add, CRing.natCast_mul, hchar, CRing.zero_mul, CRing.zero_add]

private theorem add_four_reassoc (A B C D : R) :
    (A + B) + (C + D) = (C + (A + D)) + B := by
  calc
    (A + B) + (C + D) = A + (B + (C + D)) := CRing.add_assoc _ _ _
    _ = A + ((C + D) + B) := by rw [CRing.add_comm B (C + D)]
    _ = (A + (C + D)) + B := (CRing.add_assoc _ _ _).symm
    _ = ((A + C) + D) + B := by rw [← CRing.add_assoc A C D]
    _ = ((C + A) + D) + B := by rw [CRing.add_comm A C]
    _ = (C + (A + D)) + B := by rw [CRing.add_assoc C A D]

private theorem mul_five_reassoc (S C A X U : R) :
    S * (C * ((A * X) * U)) = (S * (C * A)) * (U * X) := by
  calc
    S * (C * ((A * X) * U))
        = S * (C * (A * (X * U))) := by rw [CRing.mul_assoc A X U]
    _   = S * (C * (A * (U * X))) := by rw [CRing.mul_comm X U]
    _   = S * ((C * A) * (U * X)) := by rw [← CRing.mul_assoc C A (U * X)]
    _   = (S * (C * A)) * (U * X) := (CRing.mul_assoc S (C * A) (U * X)).symm

/-- Zero-Mathlib Binomial Theorem in an arbitrary commutative ring `R`. -/
theorem CRing.add_pow (y z : R) (k : Nat) :
    CRing.pow (y + z) k =
      sumR (k + 1) (fun d => CRing.natCast (choose k d) * (CRing.pow y d * CRing.pow z (k - d))) := by
  induction k with
  | zero =>
    simp [CRing.pow, sumR, choose, CRing.zero_add]
  | succ n ih =>
    rw [CRing.pow, ih, CRing.left_distrib]
    rw [← sumR_mul_right (n + 1) _ y, ← sumR_mul_right (n + 1) _ z]
    have hT1 :
        sumR (n + 1) (fun d =>
          CRing.natCast (choose n d) * (CRing.pow y d * CRing.pow z (n - d)) * y) =
        sumR (n + 1) (fun d =>
          CRing.natCast (choose n d) * (CRing.pow y (d + 1) * CRing.pow z (n - d))) := by
      refine sumR_congr (fun d _ => ?_)
      calc
        CRing.natCast (choose n d) * (CRing.pow y d * CRing.pow z (n - d)) * y
            = CRing.natCast (choose n d) * ((CRing.pow y d * CRing.pow z (n - d)) * y) :=
              CRing.mul_assoc _ _ _
        _   = CRing.natCast (choose n d) * (CRing.pow y d * (CRing.pow z (n - d) * y)) := by
              rw [CRing.mul_assoc (CRing.pow y d)]
        _   = CRing.natCast (choose n d) * (CRing.pow y d * (y * CRing.pow z (n - d))) := by
              rw [CRing.mul_comm (CRing.pow z (n - d)) y]
        _   = CRing.natCast (choose n d) * ((CRing.pow y d * y) * CRing.pow z (n - d)) := by
              rw [← CRing.mul_assoc (CRing.pow y d)]
        _   = CRing.natCast (choose n d) * (CRing.pow y (d + 1) * CRing.pow z (n - d)) := rfl
    have hT2 :
        sumR (n + 1) (fun d =>
          CRing.natCast (choose n d) * (CRing.pow y d * CRing.pow z (n - d)) * z) =
        CRing.natCast (choose n 0) * (CRing.pow y 0 * CRing.pow z (n + 1)) +
        sumR n (fun d =>
          CRing.natCast (choose n (d + 1)) * (CRing.pow y (d + 1) * CRing.pow z (n - d))) := by
      rw [sumR_succ_shift n]
      congr 1
      · simp only [Nat.sub_zero]
        rw [CRing.mul_assoc, CRing.mul_assoc]
        rfl
      · refine sumR_congr (fun d hd => ?_)
        have hsub : n - (d + 1) + 1 = n - d := by omega
        calc
          CRing.natCast (choose n (d + 1)) * (CRing.pow y (d + 1) * CRing.pow z (n - (d + 1))) * z
              = CRing.natCast (choose n (d + 1)) * (CRing.pow y (d + 1) * (CRing.pow z (n - (d + 1)) * z)) := by
                rw [CRing.mul_assoc, CRing.mul_assoc]
          _   = CRing.natCast (choose n (d + 1)) * (CRing.pow y (d + 1) * CRing.pow z (n - (d + 1) + 1)) := rfl
          _   = CRing.natCast (choose n (d + 1)) * (CRing.pow y (d + 1) * CRing.pow z (n - d)) := by
                rw [hsub]
    rw [hT1, hT2, sumR_succ n]
    have hRHS :
        sumR (n + 1 + 1) (fun d =>
          CRing.natCast (choose (n + 1) d) * (CRing.pow y d * CRing.pow z (n + 1 - d))) =
        CRing.natCast (choose n 0) * (CRing.pow y 0 * CRing.pow z (n + 1)) +
        sumR n (fun d =>
          (CRing.natCast (choose n d) + CRing.natCast (choose n (d + 1))) *
            (CRing.pow y (d + 1) * CRing.pow z (n - d))) +
        CRing.natCast (choose n n) * (CRing.pow y (n + 1) * CRing.pow z 0) := by
      rw [sumR_succ_shift (n + 1), sumR_succ n]
      have h0 : choose (n + 1) 0 = choose n 0 := by simp
      have hlast : choose (n + 1) (n + 1) = choose n n := by simp
      have hsubLast : n + 1 - (n + 1) = 0 := by omega
      rw [h0, hlast, hsubLast, ← CRing.add_assoc]
      congr 2
      refine sumR_congr (fun d _ => ?_)
      have hsub : n + 1 - (d + 1) = n - d := by omega
      rw [choose, CRing.natCast_add, hsub]
    rw [hRHS]
    have hMid :
        sumR n (fun d =>
          (CRing.natCast (choose n d) + CRing.natCast (choose n (d + 1))) *
            (CRing.pow y (d + 1) * CRing.pow z (n - d))) =
        sumR n (fun d => CRing.natCast (choose n d) * (CRing.pow y (d + 1) * CRing.pow z (n - d))) +
        sumR n (fun d => CRing.natCast (choose n (d + 1)) * (CRing.pow y (d + 1) * CRing.pow z (n - d))) := by
      rw [← sumR_add]
      refine sumR_congr (fun d _ => CRing.right_distrib _ _ _)
    rw [hMid]
    have hsubN : n - n = 0 := Nat.sub_self n
    rw [hsubN]
    exact add_four_reassoc _ _ _ _

end RingSums

/-! ## 2. Direct Literal `CRing` Execution and Soundness Bridge for `T1` -/

/-- Direct literal evaluation of univariate polynomial `poly` at `t` in any `CRing R`. -/
def evalPolyR {R : Type u} [CRing R] (poly : List Nat) (t : R) : R :=
  sumR poly.length (fun k => CRing.natCast (poly.getD k 0) * CRing.pow t k)

/-- Direct literal `CRing` execution of a single `Pass2Instr` (NO binomial formulas). -/
def Pass2Instr.execRing {R : Type u} [CRing R] (x : R) : R × R → Pass2Instr → R × R
  | (o, r), .addOut poly      => (o + evalPolyR poly r, r)
  | (o, r), .addWorkConst c   => (o, r + CRing.natCast c)
  | (o, r), .addInputOut lam  => (o + CRing.natCast lam * x, r)
  | (o, r), .addInputWork lam => (o, r + CRing.natCast lam * x)

/-- Direct literal `CRing` execution of a `Pass2Prog` over any `CRing R`. -/
def Pass2Prog.execRing {R : Type u} [CRing R] (x : R) : List Pass2Instr → R × R → R × R
  | [], st        => st
  | i :: rest, st => Pass2Prog.execRing x rest (i.execRing x st)

/-- Evaluate a formal bivariate coefficient table up to total degree `D` at `(u, x)`. -/
def evalState2Coeff {R : Type u} [CRing R] (D : Nat) (coeff : Nat → Nat → Nat) (u x : R) : R :=
  sumR (D + 1) (fun d =>
    sumR (d + 1) (fun dx =>
      CRing.natCast (coeff (d - dx) dx) * (CRing.pow u (d - dx) * CRing.pow x dx)))

/-- Maximum polynomial length occurring in any `addOut` instruction of `prog` (at least `1`). -/
def Pass2Prog.maxDeg : List Pass2Instr → Nat
  | [] => 1
  | .addOut poly :: rest => max poly.length (Pass2Prog.maxDeg rest)
  | _ :: rest => Pass2Prog.maxDeg rest

private theorem Pass2Prog.maxDeg_pos (prog : List Pass2Instr) : 1 ≤ Pass2Prog.maxDeg prog := by
  induction prog with
  | nil => exact Nat.le_refl 1
  | cons i rest ih =>
    cases i <;> simp only [Pass2Prog.maxDeg]
    · exact Nat.le_trans ih (Nat.le_max_right _ _)
    · exact ih
    · exact ih
    · exact ih

/-- Key trinomial identity: literal `evalPolyR poly (u + b + a*x)` matches `polyAtShiftCoeff`. -/
theorem evalPolyR_shift_eq_polyAtShiftCoeff {R : Type u} [CRing R]
    (poly : List Nat) (b a D : Nat) (hD : poly.length ≤ D + 1) (u x : R) :
    evalPolyR poly (u + CRing.natCast b + CRing.natCast a * x) =
      evalState2Coeff D (polyAtShiftCoeff poly b a) u x := by
  have hbase : u + CRing.natCast b + CRing.natCast a * x = (u + CRing.natCast a * x) + CRing.natCast b := by
    calc
      u + CRing.natCast b + CRing.natCast a * x
          = u + (CRing.natCast b + CRing.natCast a * x) := CRing.add_assoc _ _ _
      _   = u + (CRing.natCast a * x + CRing.natCast b) := by rw [CRing.add_comm (CRing.natCast b)]
      _   = (u + CRing.natCast a * x) + CRing.natCast b := (CRing.add_assoc _ _ _).symm
  unfold evalPolyR evalState2Coeff
  rw [hbase]
  have hterm : ∀ k < poly.length,
      CRing.natCast (poly.getD k 0) * CRing.pow ((u + CRing.natCast a * x) + CRing.natCast b) k =
      sumR (D + 1) (fun d =>
        CRing.natCast (poly.getD k 0 * choose k d * b ^ (k - d)) *
          CRing.pow (u + CRing.natCast a * x) d) := by
    intro k hk
    rw [CRing.add_pow (u + CRing.natCast a * x) (CRing.natCast b) k, ← sumR_mul_left]
    have hle : k + 1 ≤ D + 1 := by omega
    rw [sumR_extend hle (fun d hd1 _ => by
      have hcz : choose k d = 0 := choose_eq_zero_of_lt (by omega)
      simp [hcz])]
    refine sumR_congr (fun d _ => ?_)
    rw [CRing.natCast_mul, CRing.natCast_mul, natCast_pow]
    calc
      CRing.natCast (poly.getD k 0) *
          (CRing.natCast (choose k d) * (CRing.pow (u + CRing.natCast a * x) d * CRing.pow (CRing.natCast b) (k - d)))
          = (CRing.natCast (poly.getD k 0) * CRing.natCast (choose k d)) *
              (CRing.pow (CRing.natCast b) (k - d) * CRing.pow (u + CRing.natCast a * x) d) := by
            rw [← CRing.mul_assoc, CRing.mul_comm (CRing.pow (u + CRing.natCast a * x) d)]
      _   = (CRing.natCast (poly.getD k 0) * CRing.natCast (choose k d) * CRing.pow (CRing.natCast b) (k - d)) *
              CRing.pow (u + CRing.natCast a * x) d := (CRing.mul_assoc _ _ _).symm
  rw [sumR_congr hterm, sumR_swap]
  refine sumR_congr (fun d _ => ?_)
  rw [sumR_mul_right, ← natCast_sumNat]
  rw [CRing.add_comm u (CRing.natCast a * x), CRing.add_pow (CRing.natCast a * x) u d, ← sumR_mul_left]
  refine sumR_congr (fun dx hdx => ?_)
  have hdd : d - dx + dx = d := by omega
  simp only [polyAtShiftCoeff, hdd, CRing.natCast_mul, natCast_pow, CRing.mul_pow]
  exact mul_five_reassoc _ _ _ _ _

/-- Generalized per-program soundness invariant for `Pass2Prog.execFrom`. -/
theorem Pass2Prog.execRing_from_eq_evalState2 {R : Type u} [CRing R]
    {p : Nat} (hchar : (CRing.natCast p : R) = 0)
    (prog : List Pass2Instr) (D : Nat) (hD : Pass2Prog.maxDeg prog ≤ D)
    (st : State2) (o u x : R) :
    Pass2Prog.execRing x prog
        (o + evalState2Coeff D st.coeff u x, u + CRing.natCast st.b + CRing.natCast st.a * x) =
      let st' := Pass2Prog.execFrom p prog st
      (o + evalState2Coeff D st'.coeff u x, u + CRing.natCast st'.b + CRing.natCast st'.a * x) := by
  induction prog generalizing st with
  | nil => rfl
  | cons instr rest ih =>
    have hD_rest : Pass2Prog.maxDeg rest ≤ D := by
      cases instr <;> simp only [Pass2Prog.maxDeg] at hD
      · exact Nat.le_trans (Nat.le_max_right _ _) hD
      · exact hD
      · exact hD
      · exact hD
    cases instr with
    | addOut poly =>
      have hpoly : poly.length ≤ D + 1 := by
        simp only [Pass2Prog.maxDeg] at hD
        have := Nat.le_trans (Nat.le_max_left _ _) hD
        omega
      simp only [Pass2Prog.execRing, Pass2Instr.execRing, Pass2Prog.execFrom, Pass2Instr.exec]
      have hstep :
          (o + evalState2Coeff D st.coeff u x) + evalPolyR poly (u + CRing.natCast st.b + CRing.natCast st.a * x) =
          o + evalState2Coeff D (fun dR dx => (st.coeff dR dx + polyAtShiftCoeff poly st.b st.a dR dx) % p) u x := by
        rw [evalPolyR_shift_eq_polyAtShiftCoeff poly st.b st.a D hpoly u x, CRing.add_assoc]
        congr 1
        unfold evalState2Coeff
        rw [← sumR_add]
        refine sumR_congr (fun d _ => ?_)
        rw [← sumR_add]
        refine sumR_congr (fun dx _ => ?_)
        rw [natCast_mod_eq hchar, CRing.natCast_add, CRing.right_distrib]
      rw [hstep]
      exact ih hD_rest { st with coeff := fun dR dx => (st.coeff dR dx + polyAtShiftCoeff poly st.b st.a dR dx) % p }
    | addWorkConst c =>
      simp only [Pass2Prog.execRing, Pass2Instr.execRing, Pass2Prog.execFrom, Pass2Instr.exec]
      have hr :
          (u + CRing.natCast st.b + CRing.natCast st.a * x) + CRing.natCast c =
          u + CRing.natCast ((st.b + c) % p) + CRing.natCast st.a * x := by
        rw [natCast_mod_eq hchar, CRing.natCast_add]
        calc
          (u + CRing.natCast st.b + CRing.natCast st.a * x) + CRing.natCast c
              = (u + CRing.natCast st.b) + (CRing.natCast st.a * x + CRing.natCast c) := CRing.add_assoc _ _ _
          _   = (u + CRing.natCast st.b) + (CRing.natCast c + CRing.natCast st.a * x) := by
                rw [CRing.add_comm (CRing.natCast st.a * x)]
          _   = ((u + CRing.natCast st.b) + CRing.natCast c) + CRing.natCast st.a * x := (CRing.add_assoc _ _ _).symm
          _   = (u + (CRing.natCast st.b + CRing.natCast c)) + CRing.natCast st.a * x := by
                rw [CRing.add_assoc u]
      rw [hr]
      exact ih hD_rest { st with b := (st.b + c) % p }
    | addInputWork lam =>
      simp only [Pass2Prog.execRing, Pass2Instr.execRing, Pass2Prog.execFrom, Pass2Instr.exec]
      have hr :
          (u + CRing.natCast st.b + CRing.natCast st.a * x) + CRing.natCast lam * x =
          u + CRing.natCast st.b + CRing.natCast ((st.a + lam) % p) * x := by
        rw [natCast_mod_eq hchar, CRing.natCast_add, CRing.right_distrib, CRing.add_assoc]
      rw [hr]
      exact ih hD_rest { st with a := (st.a + lam) % p }
    | addInputOut lam =>
      have hD1 : 1 ≤ D := Nat.le_trans (Pass2Prog.maxDeg_pos rest) hD_rest
      simp only [Pass2Prog.execRing, Pass2Instr.execRing, Pass2Prog.execFrom, Pass2Instr.exec]
      have hlam :
          evalState2Coeff D (fun dR dx => if dR = 0 ∧ dx = 1 then lam else 0) u x =
          CRing.natCast lam * x := by
        unfold evalState2Coeff
        have hinner : ∀ d < D + 1,
            sumR (d + 1) (fun dx =>
              CRing.natCast (if d - dx = 0 ∧ dx = 1 then lam else 0) *
                (CRing.pow u (d - dx) * CRing.pow x dx)) =
            if d = 1 then CRing.natCast lam * x else 0 := by
          intro d _
          by_cases hd1 : d = 1
          · subst hd1
            simp [sumR, CRing.pow, CRing.zero_add, CRing.one_mul]
          · simp only [hd1, ↓reduceIte]
            refine sumR_eq_zero (fun dx hdx => ?_)
            have hcond : ¬ (d - dx = 0 ∧ dx = 1) := by omega
            simp [hcond]
        rw [sumR_congr hinner]
        exact sumR_single (by omega) (CRing.natCast lam * x)
      have hstep :
          (o + evalState2Coeff D st.coeff u x) + CRing.natCast lam * x =
          o + evalState2Coeff D (fun dR dx => (st.coeff dR dx + if dR = 0 ∧ dx = 1 then lam else 0) % p) u x := by
        rw [← hlam, CRing.add_assoc]
        congr 1
        unfold evalState2Coeff
        rw [← sumR_add]
        refine sumR_congr (fun d _ => ?_)
        rw [← sumR_add]
        refine sumR_congr (fun dx _ => ?_)
        rw [natCast_mod_eq hchar, CRing.natCast_add, CRing.right_distrib]
      rw [hstep]
      exact ih hD_rest { st with coeff := fun dR dx => (st.coeff dR dx + if dR = 0 ∧ dx = 1 then lam else 0) % p }

/--
**Exact Symbolic-to-Literal Ring Soundness for ALL `Pass2Prog`s:**
For EVERY `prog`, EVERY `p`, EVERY `CRing R` with `natCast p = 0`, and EVERY `o, u, x : R`,
literal ring execution agrees identically with symbolic `Pass2Prog.exec`.
-/
theorem Pass2Prog.execRing_eq_evalState2 {R : Type u} [CRing R]
    {p : Nat} (hchar : (CRing.natCast p : R) = 0)
    (prog : List Pass2Instr) (D : Nat) (hD : Pass2Prog.maxDeg prog ≤ D)
    (o u x : R) :
    Pass2Prog.execRing x prog (o, u) =
      let st := Pass2Prog.exec p prog
      (o + evalState2Coeff D st.coeff u x, u + CRing.natCast st.b + CRing.natCast st.a * x) := by
  have hinit :
      (o, u) =
      (o + evalState2Coeff D (fun _ _ => 0) u x,
       u + CRing.natCast 0 + CRing.natCast 0 * x) := by
    have hcz : evalState2Coeff D (fun _ _ => 0) u x = 0 := by
      unfold evalState2Coeff
      refine sumR_eq_zero (fun _ _ => sumR_eq_zero (fun _ _ => by simp))
    simp [hcz]
  conv => lhs; rw [hinit]
  exact Pass2Prog.execRing_from_eq_evalState2 hchar prog D hD ⟨0, 0, fun _ _ => 0⟩ o u x

/--
**Theorem `T1s` (Literal `CRing` Soundness of `CleanlyComputes2`):**
Whenever `CleanlyComputes2 p prog f` holds symbolically, literal ring execution of `prog` over
**every** characteristic-`p` commutative ring `R` cleanly maps `(o, u) ↦ (o + evalPolyR f x, u)`.
-/
theorem pass2_clean_implies_ring_exec {p : Nat} {prog : List Pass2Instr} {f : List Nat}
    (hclean : CleanlyComputes2 p prog f) :
    ∀ (R : Type) [CRing R], (CRing.natCast p : R) = 0 →
      ∀ o u x : R, Pass2Prog.execRing x prog (o, u) = (o + evalPolyR f x, u) := by
  intro R _ hchar o u x
  let D := max (Pass2Prog.maxDeg prog) f.length
  have hD : Pass2Prog.maxDeg prog ≤ D := Nat.le_max_left _ _
  have hfD : f.length ≤ D + 1 := by
    have := Nat.le_max_right (Pass2Prog.maxDeg prog) f.length
    omega
  rw [Pass2Prog.execRing_eq_evalState2 hchar prog D hD o u x]
  rcases hclean with ⟨hb, ha, hcoeff⟩
  have hbr : (CRing.natCast (Pass2Prog.exec p prog).b : R) = 0 := by
    rw [← natCast_mod_eq hchar, hb]; rfl
  have har : (CRing.natCast (Pass2Prog.exec p prog).a : R) = 0 := by
    rw [← natCast_mod_eq hchar, ha]; rfl
  have hO : evalState2Coeff D (Pass2Prog.exec p prog).coeff u x = evalPolyR f x := by
    unfold evalState2Coeff evalPolyR
    have hinner : ∀ d < D + 1,
        sumR (d + 1) (fun dx =>
          CRing.natCast ((Pass2Prog.exec p prog).coeff (d - dx) dx) *
            (CRing.pow u (d - dx) * CRing.pow x dx)) =
        CRing.natCast (f.getD d 0) * CRing.pow x d := by
      intro d _
      have hterm : ∀ dx < d + 1,
          CRing.natCast ((Pass2Prog.exec p prog).coeff (d - dx) dx) *
            (CRing.pow u (d - dx) * CRing.pow x dx) =
          if dx = d then CRing.natCast (f.getD d 0) * CRing.pow x d else 0 := by
        intro dx hdx
        rw [← natCast_mod_eq hchar, hcoeff (d - dx) dx, natCast_mod_eq hchar]
        by_cases hEq : dx = d
        · subst hEq
          simp [CRing.one_mul]
        · have hsub : d - dx ≠ 0 := by omega
          simp [hEq, hsub]
      rw [sumR_congr hterm]
      exact sumR_single (Nat.lt_succ_self d) _
    rw [sumR_congr hinner]
    symm
    exact sumR_extend hfD (fun d hd _ => by
      have hnone : f[d]? = none := List.getElem?_eq_none hd
      simp [List.getD, hnone])
  simp [hbr, har, hO]

/-! ## 3. Direct Literal `GF4`-Algebra Execution and Soundness Bridge for `T1e` -/

/-- Ring homomorphism `φ : GF4 → R` making an arbitrary `CRing R` a commutative `GF4`-algebra. -/
structure GF4Hom (R : Type u) [CRing R] where
  toFun : GF4 → R
  map_zero : toFun .z = 0
  map_one  : toFun .one = 1
  map_add  : ∀ a b : GF4, toFun (GF4.add a b) = toFun a + toFun b
  map_mul  : ∀ a b : GF4, toFun (GF4.mul a b) = toFun a * toFun b

/-- Identity homomorphism `GF4 → GF4` witnessing `GF4` as a `GF4`-algebra. -/
def GF4Hom.id : GF4Hom GF4 where
  toFun := fun a => a
  map_zero := rfl
  map_one  := rfl
  map_add  := fun _ _ => rfl
  map_mul  := fun _ _ => rfl

section GF4Alg

variable {R : Type u} [CRing R]

theorem GF4Hom.map_pow (φ : GF4Hom R) (a : GF4) (k : Nat) :
    φ.toFun (GF4.pow a k) = CRing.pow (φ.toFun a) k := by
  induction k with
  | zero => exact φ.map_one
  | succ m ih =>
    rw [GF4.pow, φ.map_mul, ih, CRing.pow, CRing.mul_comm]

theorem GF4Hom.char2 (φ : GF4Hom R) : (CRing.natCast 2 : R) = 0 := by
  have h1 : (CRing.natCast 2 : R) = 1 + 1 := by
    simp [CRing.natCast, CRing.zero_add]
  rw [h1, ← φ.map_one, ← φ.map_add]
  exact φ.map_zero

theorem GF4Hom.map_sumGF4 (φ : GF4Hom R) (n : Nat) (f : Nat → GF4) :
    φ.toFun (sumGF4 n f) = sumR n (fun i => φ.toFun (f i)) := by
  induction n with
  | zero => exact φ.map_zero
  | succ m ih =>
    rw [sumGF4, φ.map_add, ih, sumR_succ]

theorem GF4Hom.map_binomGF4 (φ : GF4Hom R) (n k : Nat) :
    φ.toFun (binomGF4 n k) = CRing.natCast (choose n k) := by
  rw [← natCast_mod_eq φ.char2 (choose n k)]
  unfold binomGF4
  have hlt : choose n k % 2 < 2 := Nat.mod_lt _ (by decide)
  by_cases h1 : choose n k % 2 = 1
  · simp [h1, φ.map_one]
  · have h0 : choose n k % 2 = 0 := by omega
    simp [h0, φ.map_zero]

/-- Direct literal evaluation of a polynomial over `GF4` in any `GF4`-algebra `(R, φ)`. -/
def evalPolyGF4Alg (φ : GF4Hom R) (poly : List GF4) (t : R) : R :=
  sumR poly.length (fun k => φ.toFun (poly.getD k .z) * CRing.pow t k)

/-- Direct literal `GF4`-algebra execution of a single `Pass2GF4Instr` (NO binomial formulas). -/
def Pass2GF4Instr.execAlg (φ : GF4Hom R) (x : R) : R × R → Pass2GF4Instr → R × R
  | (o, r), .addOut poly      => (o + evalPolyGF4Alg φ poly r, r)
  | (o, r), .addWorkConst c   => (o, r + φ.toFun c)
  | (o, r), .addInputOut lam  => (o + φ.toFun lam * x, r)
  | (o, r), .addInputWork lam => (o, r + φ.toFun lam * x)

/-- Direct literal `GF4`-algebra execution of a `Pass2GF4Prog`. -/
def Pass2GF4Prog.execAlg (φ : GF4Hom R) (x : R) : List Pass2GF4Instr → R × R → R × R
  | [], st        => st
  | i :: rest, st => Pass2GF4Prog.execAlg φ x rest (i.execAlg φ x st)

/-- Evaluate a formal `GF4` bivariate coefficient table up to total degree `D` in `(R, φ)`. -/
def evalState2GF4Coeff (φ : GF4Hom R) (D : Nat) (coeff : Nat → Nat → GF4) (u x : R) : R :=
  sumR (D + 1) (fun d =>
    sumR (d + 1) (fun dx =>
      φ.toFun (coeff (d - dx) dx) * (CRing.pow u (d - dx) * CRing.pow x dx)))

/-- Maximum polynomial length occurring in any `addOut` instruction of a `Pass2GF4Prog`. -/
def Pass2GF4Prog.maxDeg : List Pass2GF4Instr → Nat
  | [] => 1
  | .addOut poly :: rest => max poly.length (Pass2GF4Prog.maxDeg rest)
  | _ :: rest => Pass2GF4Prog.maxDeg rest

private theorem Pass2GF4Prog.maxDeg_pos (prog : List Pass2GF4Instr) : 1 ≤ Pass2GF4Prog.maxDeg prog := by
  induction prog with
  | nil => exact Nat.le_refl 1
  | cons i rest ih =>
    cases i <;> simp only [Pass2GF4Prog.maxDeg]
    · exact Nat.le_trans ih (Nat.le_max_right _ _)
    · exact ih
    · exact ih
    · exact ih

theorem evalPolyGF4Alg_shift_eq_polyAtShiftCoeffGF4 (φ : GF4Hom R)
    (poly : List GF4) (b a : GF4) (D : Nat) (hD : poly.length ≤ D + 1) (u x : R) :
    evalPolyGF4Alg φ poly (u + φ.toFun b + φ.toFun a * x) =
      evalState2GF4Coeff φ D (polyAtShiftCoeffGF4 poly b a) u x := by
  have hbase : u + φ.toFun b + φ.toFun a * x = (u + φ.toFun a * x) + φ.toFun b := by
    calc
      u + φ.toFun b + φ.toFun a * x
          = u + (φ.toFun b + φ.toFun a * x) := CRing.add_assoc _ _ _
      _   = u + (φ.toFun a * x + φ.toFun b) := by rw [CRing.add_comm (φ.toFun b)]
      _   = (u + φ.toFun a * x) + φ.toFun b := (CRing.add_assoc _ _ _).symm
  unfold evalPolyGF4Alg evalState2GF4Coeff
  rw [hbase]
  have hterm : ∀ k < poly.length,
      φ.toFun (poly.getD k .z) * CRing.pow ((u + φ.toFun a * x) + φ.toFun b) k =
      sumR (D + 1) (fun d =>
        φ.toFun (GF4.mul (poly.getD k .z) (GF4.mul (binomGF4 k d) (GF4.pow b (k - d)))) *
          CRing.pow (u + φ.toFun a * x) d) := by
    intro k hk
    rw [CRing.add_pow (u + φ.toFun a * x) (φ.toFun b) k, ← sumR_mul_left]
    have hle : k + 1 ≤ D + 1 := by omega
    rw [sumR_extend hle (fun d hd1 _ => by
      have hcz : choose k d = 0 := choose_eq_zero_of_lt (by omega)
      simp [hcz])]
    refine sumR_congr (fun d _ => ?_)
    rw [φ.map_mul, φ.map_mul, φ.map_binomGF4, φ.map_pow]
    calc
      φ.toFun (poly.getD k .z) *
          (CRing.natCast (choose k d) * (CRing.pow (u + φ.toFun a * x) d * CRing.pow (φ.toFun b) (k - d)))
          = φ.toFun (poly.getD k .z) *
              (CRing.natCast (choose k d) * (CRing.pow (φ.toFun b) (k - d) * CRing.pow (u + φ.toFun a * x) d)) := by
            rw [CRing.mul_comm (CRing.pow (u + φ.toFun a * x) d)]
      _   = φ.toFun (poly.getD k .z) *
              ((CRing.natCast (choose k d) * CRing.pow (φ.toFun b) (k - d)) * CRing.pow (u + φ.toFun a * x) d) := by
            rw [← CRing.mul_assoc (CRing.natCast (choose k d))]
      _   = (φ.toFun (poly.getD k .z) * (CRing.natCast (choose k d) * CRing.pow (φ.toFun b) (k - d))) *
              CRing.pow (u + φ.toFun a * x) d := (CRing.mul_assoc _ _ _).symm
  rw [sumR_congr hterm, sumR_swap]
  refine sumR_congr (fun d _ => ?_)
  rw [sumR_mul_right, ← φ.map_sumGF4]
  rw [CRing.add_comm u (φ.toFun a * x), CRing.add_pow (φ.toFun a * x) u d, ← sumR_mul_left]
  refine sumR_congr (fun dx hdx => ?_)
  have hdd : d - dx + dx = d := by omega
  simp only [polyAtShiftCoeffGF4, hdd, φ.map_mul, φ.map_binomGF4, φ.map_pow, CRing.mul_pow]
  exact mul_five_reassoc _ _ _ _ _

theorem Pass2GF4Prog.execAlg_from_eq_evalState2GF4 (φ : GF4Hom R)
    (prog : List Pass2GF4Instr) (D : Nat) (hD : Pass2GF4Prog.maxDeg prog ≤ D)
    (st : State2GF4) (o u x : R) :
    Pass2GF4Prog.execAlg φ x prog
        (o + evalState2GF4Coeff φ D st.coeff u x, u + φ.toFun st.b + φ.toFun st.a * x) =
      let st' := Pass2GF4Prog.execFrom prog st
      (o + evalState2GF4Coeff φ D st'.coeff u x, u + φ.toFun st'.b + φ.toFun st'.a * x) := by
  induction prog generalizing st with
  | nil => rfl
  | cons instr rest ih =>
    have hD_rest : Pass2GF4Prog.maxDeg rest ≤ D := by
      cases instr <;> simp only [Pass2GF4Prog.maxDeg] at hD
      · exact Nat.le_trans (Nat.le_max_right _ _) hD
      · exact hD
      · exact hD
      · exact hD
    cases instr with
    | addOut poly =>
      have hpoly : poly.length ≤ D + 1 := by
        simp only [Pass2GF4Prog.maxDeg] at hD
        have := Nat.le_trans (Nat.le_max_left _ _) hD
        omega
      simp only [Pass2GF4Prog.execAlg, Pass2GF4Instr.execAlg, Pass2GF4Prog.execFrom, Pass2GF4Instr.exec]
      have hstep :
          (o + evalState2GF4Coeff φ D st.coeff u x) + evalPolyGF4Alg φ poly (u + φ.toFun st.b + φ.toFun st.a * x) =
          o + evalState2GF4Coeff φ D (fun dR dx => GF4.add (st.coeff dR dx) (polyAtShiftCoeffGF4 poly st.b st.a dR dx)) u x := by
        rw [evalPolyGF4Alg_shift_eq_polyAtShiftCoeffGF4 φ poly st.b st.a D hpoly u x, CRing.add_assoc]
        congr 1
        unfold evalState2GF4Coeff
        rw [← sumR_add]
        refine sumR_congr (fun d _ => ?_)
        rw [← sumR_add]
        refine sumR_congr (fun dx _ => ?_)
        rw [φ.map_add, CRing.right_distrib]
      rw [hstep]
      exact ih hD_rest { st with coeff := fun dR dx => GF4.add (st.coeff dR dx) (polyAtShiftCoeffGF4 poly st.b st.a dR dx) }
    | addWorkConst c =>
      simp only [Pass2GF4Prog.execAlg, Pass2GF4Instr.execAlg, Pass2GF4Prog.execFrom, Pass2GF4Instr.exec]
      have hr :
          (u + φ.toFun st.b + φ.toFun st.a * x) + φ.toFun c =
          u + φ.toFun (GF4.add st.b c) + φ.toFun st.a * x := by
        rw [φ.map_add]
        calc
          (u + φ.toFun st.b + φ.toFun st.a * x) + φ.toFun c
              = (u + φ.toFun st.b) + (φ.toFun st.a * x + φ.toFun c) := CRing.add_assoc _ _ _
          _   = (u + φ.toFun st.b) + (φ.toFun c + φ.toFun st.a * x) := by
                rw [CRing.add_comm (φ.toFun st.a * x)]
          _   = ((u + φ.toFun st.b) + φ.toFun c) + φ.toFun st.a * x := (CRing.add_assoc _ _ _).symm
          _   = (u + (φ.toFun st.b + φ.toFun c)) + φ.toFun st.a * x := by
                rw [CRing.add_assoc u]
      rw [hr]
      exact ih hD_rest { st with b := GF4.add st.b c }
    | addInputWork lam =>
      simp only [Pass2GF4Prog.execAlg, Pass2GF4Instr.execAlg, Pass2GF4Prog.execFrom, Pass2GF4Instr.exec]
      have hr :
          (u + φ.toFun st.b + φ.toFun st.a * x) + φ.toFun lam * x =
          u + φ.toFun st.b + φ.toFun (GF4.add st.a lam) * x := by
        rw [φ.map_add, CRing.right_distrib, CRing.add_assoc]
      rw [hr]
      exact ih hD_rest { st with a := GF4.add st.a lam }
    | addInputOut lam =>
      have hD1 : 1 ≤ D := Nat.le_trans (Pass2GF4Prog.maxDeg_pos rest) hD_rest
      simp only [Pass2GF4Prog.execAlg, Pass2GF4Instr.execAlg, Pass2GF4Prog.execFrom, Pass2GF4Instr.exec]
      have hlam :
          evalState2GF4Coeff φ D (fun dR dx => if dR = 0 ∧ dx = 1 then lam else .z) u x =
          φ.toFun lam * x := by
        unfold evalState2GF4Coeff
        have hinner : ∀ d < D + 1,
            sumR (d + 1) (fun dx =>
              φ.toFun (if d - dx = 0 ∧ dx = 1 then lam else .z) *
                (CRing.pow u (d - dx) * CRing.pow x dx)) =
            if d = 1 then φ.toFun lam * x else 0 := by
          intro d _
          by_cases hd1 : d = 1
          · subst hd1
            simp [sumR, CRing.pow, CRing.zero_add, CRing.one_mul, φ.map_zero]
          · simp only [hd1, ↓reduceIte]
            refine sumR_eq_zero (fun dx hdx => ?_)
            have hcond : ¬ (d - dx = 0 ∧ dx = 1) := by omega
            simp [hcond, φ.map_zero]
        rw [sumR_congr hinner]
        exact sumR_single (by omega) (φ.toFun lam * x)
      have hstep :
          (o + evalState2GF4Coeff φ D st.coeff u x) + φ.toFun lam * x =
          o + evalState2GF4Coeff φ D (fun dR dx => GF4.add (st.coeff dR dx) (if dR = 0 ∧ dx = 1 then lam else .z)) u x := by
        rw [← hlam, CRing.add_assoc]
        congr 1
        unfold evalState2GF4Coeff
        rw [← sumR_add]
        refine sumR_congr (fun d _ => ?_)
        rw [← sumR_add]
        refine sumR_congr (fun dx _ => ?_)
        rw [φ.map_add, CRing.right_distrib]
      rw [hstep]
      exact ih hD_rest { st with coeff := fun dR dx => GF4.add (st.coeff dR dx) (if dR = 0 ∧ dx = 1 then lam else .z) }

theorem Pass2GF4Prog.execAlg_eq_evalState2GF4 (φ : GF4Hom R)
    (prog : List Pass2GF4Instr) (D : Nat) (hD : Pass2GF4Prog.maxDeg prog ≤ D)
    (o u x : R) :
    Pass2GF4Prog.execAlg φ x prog (o, u) =
      let st := Pass2GF4Prog.exec prog
      (o + evalState2GF4Coeff φ D st.coeff u x, u + φ.toFun st.b + φ.toFun st.a * x) := by
  have hinit :
      (o, u) =
      (o + evalState2GF4Coeff φ D (fun _ _ => .z) u x,
       u + φ.toFun .z + φ.toFun .z * x) := by
    have hcz : evalState2GF4Coeff φ D (fun _ _ => .z) u x = 0 := by
      unfold evalState2GF4Coeff
      refine sumR_eq_zero (fun _ _ => sumR_eq_zero (fun _ _ => by simp [φ.map_zero]))
    simp [hcz, φ.map_zero]
  conv => lhs; rw [hinit]
  exact Pass2GF4Prog.execAlg_from_eq_evalState2GF4 φ prog D hD ⟨.z, .z, fun _ _ => .z⟩ o u x

end GF4Alg

/--
**Theorem `T1es` (Literal `GF4`-Algebra Soundness of `CleanlyComputes2GF4`):**
Whenever `CleanlyComputes2GF4 prog f` holds symbolically, literal execution of `prog` over
**every** commutative `GF4`-algebra `(R, φ)` (including `GF4` itself via `GF4Hom.id`)
cleanly maps `(o, u) ↦ (o + evalPolyGF4Alg φ f x, u)`.
-/
theorem pass2gf4_clean_implies_alg_exec {prog : List Pass2GF4Instr} {f : List GF4}
    (hclean : CleanlyComputes2GF4 prog f) :
    ∀ (R : Type) [CRing R] (φ : GF4Hom R) (o u x : R),
      Pass2GF4Prog.execAlg φ x prog (o, u) = (o + evalPolyGF4Alg φ f x, u) := by
  intro R _ φ o u x
  let D := max (Pass2GF4Prog.maxDeg prog) f.length
  have hD : Pass2GF4Prog.maxDeg prog ≤ D := Nat.le_max_left _ _
  have hfD : f.length ≤ D + 1 := by
    have := Nat.le_max_right (Pass2GF4Prog.maxDeg prog) f.length
    omega
  rw [Pass2GF4Prog.execAlg_eq_evalState2GF4 φ prog D hD o u x]
  rcases hclean with ⟨hb, ha, hcoeff⟩
  have hO : evalState2GF4Coeff φ D (Pass2GF4Prog.exec prog).coeff u x = evalPolyGF4Alg φ f x := by
    unfold evalState2GF4Coeff evalPolyGF4Alg
    have hinner : ∀ d < D + 1,
        sumR (d + 1) (fun dx =>
          φ.toFun ((Pass2GF4Prog.exec prog).coeff (d - dx) dx) *
            (CRing.pow u (d - dx) * CRing.pow x dx)) =
        φ.toFun (f.getD d .z) * CRing.pow x d := by
      intro d _
      have hterm : ∀ dx < d + 1,
          φ.toFun ((Pass2GF4Prog.exec prog).coeff (d - dx) dx) *
            (CRing.pow u (d - dx) * CRing.pow x dx) =
          if dx = d then φ.toFun (f.getD d .z) * CRing.pow x d else 0 := by
        intro dx hdx
        rw [hcoeff (d - dx) dx]
        by_cases hEq : dx = d
        · subst hEq
          simp [CRing.one_mul]
        · have hsub : d - dx ≠ 0 := by omega
          simp [hEq, hsub, φ.map_zero]
      rw [sumR_congr hterm]
      exact sumR_single (Nat.lt_succ_self d) _
    rw [sumR_congr hinner]
    symm
    exact sumR_extend hfD (fun d hd _ => by
      have hnone : f[d]? = none := List.getElem?_eq_none hd
      simp [List.getD, hnone, φ.map_zero])
  simp [hb, ha, φ.map_zero, hO]

/-! ## 4. Formal Power Series Ring `R[[X]]` and Converse Completeness (`T1sc`, `T1esc`) -/

/-- Univariate formal power series `R[[X]]` over an arbitrary commutative ring `R` (zero Mathlib). -/
structure FPS (R : Type u) where
  coeff : Nat → R

theorem FPS.ext {R : Type u} {f g : FPS R} (h : ∀ n : Nat, f.coeff n = g.coeff n) : f = g := by
  cases f; cases g; congr; funext n; exact h n

section FPSRing

variable {R : Type u} [CRing R]

private theorem sumR_rev (n : Nat) (f : Nat → R) :
    sumR (n + 1) (fun i => f (n - i)) = sumR (n + 1) f := by
  induction n with
  | zero => simp [sumR]
  | succ m ih =>
    rw [sumR_succ_shift (m + 1) (fun i => f (m + 1 - i))]
    have hsub0 : m + 1 - 0 = m + 1 := Nat.sub_zero (m + 1)
    have hshift :
        sumR (m + 1) (fun i => f (m + 1 - (i + 1))) = sumR (m + 1) (fun i => f (m - i)) :=
      sumR_congr (fun i _ => by rw [Nat.succ_sub_succ_eq_sub])
    rw [hsub0, hshift, ih, CRing.add_comm, ← sumR_succ]

private theorem sumR_shift_ge {m : Nat} (i : Nat) (hi : i ≤ m) (g : Nat → R) :
    sumR (m + 1) (fun k => if i ≤ k then g k else 0) = sumR (m - i + 1) (fun j => g (i + j)) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hi
  have hsub : i + d - i = d := Nat.add_sub_cancel_left i d
  rw [hsub]
  clear hi hsub
  induction d with
  | zero =>
    simp only [Nat.add_zero, sumR_succ, sumR_zero, CRing.zero_add, Nat.le_refl, ↓reduceIte]
    have hz : sumR i (fun k => if i ≤ k then g k else 0) = 0 :=
      sumR_eq_zero (fun k hk => by
        have hnot : ¬ (i ≤ k) := by omega
        simp only [hnot, ↓reduceIte])
    rw [hz, CRing.zero_add]
  | succ d' ih =>
    have hstep : i + (d' + 1) + 1 = (i + d' + 1) + 1 := by omega
    rw [hstep, sumR_succ, ih]
    have hle : i ≤ i + d' + 1 := by omega
    simp only [hle, ↓reduceIte]
    have heq : i + d' + 1 = i + (d' + 1) := by omega
    rw [heq, ← sumR_succ]

instance : Zero (FPS R) := ⟨⟨fun _ => 0⟩⟩
instance : One (FPS R) := ⟨⟨fun i => if i = 0 then 1 else 0⟩⟩
instance : Add (FPS R) := ⟨fun f g => ⟨fun i => f.coeff i + g.coeff i⟩⟩
instance : Neg (FPS R) := ⟨fun f => ⟨fun i => -(f.coeff i)⟩⟩
instance : Mul (FPS R) :=
  ⟨fun f g => ⟨fun n => sumR (n + 1) (fun i => f.coeff i * g.coeff (n - i))⟩⟩

instance instCRingFPS : CRing (FPS R) where
  add_assoc a b c := FPS.ext (fun n => CRing.add_assoc (a.coeff n) (b.coeff n) (c.coeff n))
  add_comm a b := FPS.ext (fun n => CRing.add_comm (a.coeff n) (b.coeff n))
  zero_add a := FPS.ext (fun n => CRing.zero_add (a.coeff n))
  add_neg a := FPS.ext (fun n => CRing.add_neg (a.coeff n))
  one_mul a := by
    apply FPS.ext; intro n
    change sumR (n + 1) (fun i => (if i = 0 then (1 : R) else 0) * a.coeff (n - i)) = a.coeff n
    have hterm : ∀ i < n + 1,
        (if i = 0 then (1 : R) else 0) * a.coeff (n - i) = if i = 0 then a.coeff n else 0 := by
      intro i _
      by_cases hi : i = 0
      · subst hi; simp [CRing.one_mul]
      · simp [hi]
    rw [sumR_congr hterm]
    exact sumR_single (Nat.zero_lt_succ n) (a.coeff n)
  mul_comm a b := by
    apply FPS.ext; intro n
    change sumR (n + 1) (fun i => a.coeff i * b.coeff (n - i)) =
      sumR (n + 1) (fun i => b.coeff i * a.coeff (n - i))
    rw [← sumR_rev n (fun i => a.coeff i * b.coeff (n - i))]
    refine sumR_congr (fun i hi => ?_)
    have hsub : n - (n - i) = i := by omega
    rw [hsub, CRing.mul_comm]
  left_distrib a b c := by
    apply FPS.ext; intro n
    change sumR (n + 1) (fun i => a.coeff i * (b.coeff (n - i) + c.coeff (n - i))) =
      sumR (n + 1) (fun i => a.coeff i * b.coeff (n - i)) +
      sumR (n + 1) (fun i => a.coeff i * c.coeff (n - i))
    rw [← sumR_add]
    exact sumR_congr (fun i _ => CRing.left_distrib _ _ _)
  mul_assoc a b c := by
    apply FPS.ext; intro n
    change sumR (n + 1) (fun k => sumR (k + 1) (fun i => a.coeff i * b.coeff (k - i)) * c.coeff (n - k)) =
      sumR (n + 1) (fun i => a.coeff i * sumR (n - i + 1) (fun j => b.coeff j * c.coeff (n - i - j)))
    have h1 :
        sumR (n + 1) (fun k => sumR (k + 1) (fun i => a.coeff i * b.coeff (k - i)) * c.coeff (n - k)) =
        sumR (n + 1) (fun k => sumR (n + 1) (fun i => if i ≤ k then a.coeff i * b.coeff (k - i) * c.coeff (n - k) else 0)) := by
      refine sumR_congr (fun k hk => ?_)
      rw [← sumR_mul_right]
      have hinner :
          sumR (k + 1) (fun i => a.coeff i * b.coeff (k - i) * c.coeff (n - k)) =
          sumR (k + 1) (fun i => if i ≤ k then a.coeff i * b.coeff (k - i) * c.coeff (n - k) else 0) :=
        sumR_congr (fun i hi => by
          have hle : i ≤ k := by omega
          simp only [hle, ↓reduceIte])
      rw [hinner]
      exact sumR_extend (by omega) (fun i hi1 _ => by
        have hnot : ¬ (i ≤ k) := by omega
        simp only [hnot, ↓reduceIte])
    rw [h1, sumR_swap]
    refine sumR_congr (fun i hi => ?_)
    rw [sumR_shift_ge i (by omega) (fun k => a.coeff i * b.coeff (k - i) * c.coeff (n - k)), ← sumR_mul_left]
    refine sumR_congr (fun j _ => ?_)
    have hsub1 : i + j - i = j := Nat.add_sub_cancel_left i j
    have hsub2 : n - (i + j) = n - i - j := Nat.sub_add_eq n i j
    rw [hsub1, hsub2, CRing.mul_assoc]

/-- Constant embedding `R → R[[X]]`. -/
def FPS.const (c : R) : FPS R := ⟨fun i => if i = 0 then c else 0⟩

/-- Formal indeterminate `X ∈ R[[X]]`. -/
def FPS.var : FPS R := ⟨fun i => if i = 1 then 1 else 0⟩

theorem FPS.const_zero : (FPS.const (0 : R) : FPS R) = 0 := by
  apply FPS.ext; intro n
  change (if n = 0 then (0 : R) else 0) = 0
  split <;> rfl

theorem FPS.const_one : (FPS.const (1 : R) : FPS R) = 1 := rfl

theorem FPS.const_add (a b : R) : FPS.const (a + b) = FPS.const a + FPS.const b := by
  apply FPS.ext; intro n
  change (if n = 0 then a + b else 0) = (if n = 0 then a else 0) + (if n = 0 then b else 0)
  by_cases hn : n = 0 <;> simp [hn]

theorem FPS.const_mul_coeff (c : R) (f : FPS R) (n : Nat) :
    (FPS.const c * f).coeff n = c * f.coeff n := by
  change sumR (n + 1) (fun i => (if i = 0 then c else 0) * f.coeff (n - i)) = c * f.coeff n
  have hterm : ∀ i < n + 1,
      (if i = 0 then c else 0) * f.coeff (n - i) = if i = 0 then c * f.coeff n else 0 := by
    intro i _
    by_cases hi : i = 0
    · subst hi; simp
    · simp [hi]
  rw [sumR_congr hterm]
  exact sumR_single (Nat.zero_lt_succ n) (c * f.coeff n)

theorem FPS.const_mul (a b : R) : FPS.const (a * b) = FPS.const a * FPS.const b := by
  apply FPS.ext; intro n
  rw [FPS.const_mul_coeff]
  change (if n = 0 then a * b else 0) = a * (if n = 0 then b else 0)
  by_cases hn : n = 0 <;> simp [hn]

theorem FPS.natCast_eq (k : Nat) : (CRing.natCast k : FPS R) = FPS.const (CRing.natCast k) := by
  induction k with
  | zero => exact FPS.const_zero.symm
  | succ m ih =>
    change (CRing.natCast m : FPS R) + 1 = FPS.const (CRing.natCast m + 1)
    rw [ih, ← FPS.const_one, ← FPS.const_add]

theorem FPS.const_pow (a : R) (k : Nat) : CRing.pow (FPS.const a) k = FPS.const (CRing.pow a k) := by
  induction k with
  | zero => exact FPS.const_one.symm
  | succ m ih =>
    simp only [CRing.pow, ih, ← FPS.const_mul]

theorem FPS.var_pow_coeff (k n : Nat) :
    (CRing.pow (FPS.var : FPS R) k).coeff n = if n = k then 1 else 0 := by
  induction k generalizing n with
  | zero => rfl
  | succ m ih =>
    change sumR (n + 1) (fun i => (CRing.pow (FPS.var : FPS R) m).coeff i * (if n - i = 1 then (1 : R) else 0)) = _
    have hterm : ∀ i < n + 1,
        (CRing.pow (FPS.var : FPS R) m).coeff i * (if n - i = 1 then (1 : R) else 0) =
        if i = m then (if n = m + 1 then (1 : R) else 0) else 0 := by
      intro i hi
      rw [ih i]
      by_cases him : i = m
      · subst him
        by_cases hnm : n = i + 1
        · subst hnm; simp
        · have hsub : n - i ≠ 1 := by omega
          simp [hnm, hsub]
      · simp [him]
    rw [sumR_congr hterm]
    by_cases hmn : m < n + 1
    · exact sumR_single hmn _
    · have hne : n ≠ m + 1 := by omega
      simp only [hne, ↓reduceIte]
      exact sumR_eq_zero (fun i hi => by
        have him : i ≠ m := by omega
        simp [him])

theorem FPS.sumR_coeff (n : Nat) (f : Nat → FPS R) (j : Nat) :
    (sumR n f).coeff j = sumR n (fun k => (f k).coeff j) := by
  induction n with
  | zero => rfl
  | succ m ih =>
    change (sumR m f).coeff j + (f m).coeff j = sumR m (fun k => (f k).coeff j) + (f m).coeff j
    rw [ih]

/-- Lift any `GF4Hom R` to a `GF4Hom (FPS R)` via constant power series. -/
def FPS.constGF4Hom (φ : GF4Hom R) : GF4Hom (FPS R) where
  toFun := fun a => FPS.const (φ.toFun a)
  map_zero := by rw [φ.map_zero]; exact FPS.const_zero
  map_one := by rw [φ.map_one]; exact FPS.const_one
  map_add := fun a b => by rw [φ.map_add, FPS.const_add]
  map_mul := fun a b => by rw [φ.map_mul, FPS.const_mul]

end FPSRing

section FPS2Extract

variable {R : Type u} [CRing R]

private theorem fps2_monomial_coeff (a : R) (dR dx j i : Nat) :
    ((FPS.const (FPS.const a) * (CRing.pow (FPS.const FPS.var) dR * CRing.pow (FPS.var : FPS (FPS R)) dx)).coeff j).coeff i =
      if j = dx ∧ i = dR then a else 0 := by
  rw [FPS.const_pow, ← CRing.mul_assoc, ← FPS.const_mul, FPS.const_mul_coeff, FPS.var_pow_coeff]
  by_cases hj : j = dx
  · subst hj
    simp only [↓reduceIte, CRing.mul_one, true_and]
    rw [FPS.const_mul_coeff, FPS.var_pow_coeff]
    by_cases hi : i = dR <;> simp [hi]
  · simp only [hj, ↓reduceIte, CRing.mul_zero, false_and]
    rfl

private theorem evalState2Coeff_fps2_coeff (D : Nat) (coeff : Nat → Nat → Nat) (dR dx : Nat) :
    ((evalState2Coeff D coeff (FPS.const FPS.var) (FPS.var : FPS (FPS R))).coeff dx).coeff dR =
      if dR + dx ≤ D then (CRing.natCast (coeff dR dx) : R) else 0 := by
  unfold evalState2Coeff
  rw [FPS.sumR_coeff, FPS.sumR_coeff]
  have houter : ∀ d < D + 1,
      (sumR (d + 1) (fun dx' =>
        CRing.natCast (coeff (d - dx') dx') *
          (CRing.pow (FPS.const FPS.var) (d - dx') * CRing.pow (FPS.var : FPS (FPS R)) dx'))
        |>.coeff dx).coeff dR =
      if d = dR + dx then (CRing.natCast (coeff dR dx) : R) else 0 := by
    intro d _
    rw [FPS.sumR_coeff, FPS.sumR_coeff]
    have hinner : ∀ dx' < d + 1,
        ((CRing.natCast (coeff (d - dx') dx') *
          (CRing.pow (FPS.const FPS.var) (d - dx') * CRing.pow (FPS.var : FPS (FPS R)) dx')).coeff dx).coeff dR =
        if dx' = dx then (if d = dR + dx then (CRing.natCast (coeff dR dx) : R) else 0) else 0 := by
      intro dx' hdx'
      rw [FPS.natCast_eq, FPS.natCast_eq, fps2_monomial_coeff]
      by_cases h1 : dx' = dx
      · subst h1
        by_cases h2 : d = dR + dx'
        · subst h2
          have hsub : dR + dx' - dx' = dR := Nat.add_sub_cancel dR dx'
          simp [hsub]
        · have hne : dR ≠ d - dx' := by omega
          simp [h2, hne]
      · have hne : dx ≠ dx' := fun h => h1 h.symm
        simp [h1, hne]
    rw [sumR_congr hinner]
    by_cases hdx_lt : dx < d + 1
    · exact sumR_single hdx_lt _
    · have hne : d ≠ dR + dx := by omega
      simp only [hne, ↓reduceIte]
      exact sumR_eq_zero (fun dx' hdx' => by
        have hne' : dx' ≠ dx := by omega
        simp [hne'])
  rw [sumR_congr houter]
  by_cases hle : dR + dx ≤ D
  · simp only [hle, ↓reduceIte]
    exact sumR_single (by omega) _
  · simp only [hle, ↓reduceIte]
    exact sumR_eq_zero (fun d hd => by
      have hne : d ≠ dR + dx := by omega
      simp [hne])

private theorem evalPolyR_fps2_coeff (f : List Nat) (dR dx : Nat) :
    ((evalPolyR f (FPS.var : FPS (FPS R))).coeff dx).coeff dR =
      if dR = 0 then (CRing.natCast (f.getD dx 0) : R) else 0 := by
  unfold evalPolyR
  rw [FPS.sumR_coeff, FPS.sumR_coeff]
  have hterm : ∀ k < f.length,
      ((CRing.natCast (f.getD k 0) * CRing.pow (FPS.var : FPS (FPS R)) k).coeff dx).coeff dR =
      if k = dx then (if dR = 0 then (CRing.natCast (f.getD dx 0) : R) else 0) else 0 := by
    intro k _
    rw [FPS.natCast_eq, FPS.natCast_eq, FPS.const_mul_coeff, FPS.var_pow_coeff]
    by_cases hk : k = dx
    · subst hk
      simp only [↓reduceIte, CRing.mul_one]
      rfl
    · have hne : dx ≠ k := fun h => hk h.symm
      simp only [hk, hne, ↓reduceIte, CRing.mul_zero]
      rfl
  rw [sumR_congr hterm]
  by_cases hlt : dx < f.length
  · exact sumR_single hlt _
  · have hnone : f[dx]? = none := List.getElem?_eq_none (by omega)
    have hget : f.getD dx 0 = 0 := by simp [List.getD, hnone]
    have hrhs : (if dR = 0 then (CRing.natCast (f.getD dx 0) : R) else 0) = 0 := by
      rw [hget]; split <;> rfl
    rw [hrhs]
    exact sumR_eq_zero (fun k hk => by
      have hne : k ≠ dx := by omega
      simp [hne])

private theorem evalState2GF4Coeff_fps2_coeff (D : Nat) (coeff : Nat → Nat → GF4) (dR dx : Nat) :
    ((evalState2GF4Coeff (FPS.constGF4Hom (FPS.constGF4Hom GF4Hom.id)) D coeff
        (FPS.const FPS.var) (FPS.var : FPS (FPS GF4))).coeff dx).coeff dR =
      if dR + dx ≤ D then coeff dR dx else .z := by
  unfold evalState2GF4Coeff
  rw [FPS.sumR_coeff, FPS.sumR_coeff]
  have houter : ∀ d < D + 1,
      (sumR (d + 1) (fun dx' =>
        (FPS.constGF4Hom (FPS.constGF4Hom GF4Hom.id)).toFun (coeff (d - dx') dx') *
          (CRing.pow (FPS.const FPS.var) (d - dx') * CRing.pow (FPS.var : FPS (FPS GF4)) dx'))
        |>.coeff dx).coeff dR =
      if d = dR + dx then coeff dR dx else .z := by
    intro d _
    rw [FPS.sumR_coeff, FPS.sumR_coeff]
    have hinner : ∀ dx' < d + 1,
        (((FPS.constGF4Hom (FPS.constGF4Hom GF4Hom.id)).toFun (coeff (d - dx') dx') *
          (CRing.pow (FPS.const FPS.var) (d - dx') * CRing.pow (FPS.var : FPS (FPS GF4)) dx')).coeff dx).coeff dR =
        if dx' = dx then (if d = dR + dx then coeff dR dx else .z) else .z := by
      intro dx' hdx'
      change ((FPS.const (FPS.const (coeff (d - dx') dx')) *
        (CRing.pow (FPS.const FPS.var) (d - dx') * CRing.pow (FPS.var : FPS (FPS GF4)) dx')).coeff dx).coeff dR = _
      rw [fps2_monomial_coeff]
      by_cases h1 : dx' = dx
      · subst h1
        by_cases h2 : d = dR + dx'
        · subst h2
          have hsub : dR + dx' - dx' = dR := Nat.add_sub_cancel dR dx'
          simp [hsub]
        · have hne : dR ≠ d - dx' := by omega
          simp [h2, hne]; rfl
      · have hne : dx ≠ dx' := fun h => h1 h.symm
        simp [h1, hne]; rfl
    rw [sumR_congr hinner]
    by_cases hdx_lt : dx < d + 1
    · exact sumR_single hdx_lt _
    · have hne : d ≠ dR + dx := by omega
      simp only [hne, ↓reduceIte]
      exact sumR_eq_zero (fun dx' hdx' => by
        have hne' : dx' ≠ dx := by omega
        simp [hne']; rfl)
  rw [sumR_congr houter]
  by_cases hle : dR + dx ≤ D
  · simp only [hle, ↓reduceIte]
    exact sumR_single (by omega) _
  · simp only [hle, ↓reduceIte]
    exact sumR_eq_zero (fun d hd => by
      have hne : d ≠ dR + dx := by omega
      simp [hne]; rfl)

private theorem evalPolyGF4Alg_fps2_coeff (f : List GF4) (dR dx : Nat) :
    ((evalPolyGF4Alg (FPS.constGF4Hom (FPS.constGF4Hom GF4Hom.id)) f
        (FPS.var : FPS (FPS GF4))).coeff dx).coeff dR =
      if dR = 0 then f.getD dx .z else .z := by
  unfold evalPolyGF4Alg
  rw [FPS.sumR_coeff, FPS.sumR_coeff]
  have hterm : ∀ k < f.length,
      (((FPS.constGF4Hom (FPS.constGF4Hom GF4Hom.id)).toFun (f.getD k .z) *
        CRing.pow (FPS.var : FPS (FPS GF4)) k).coeff dx).coeff dR =
      if k = dx then (if dR = 0 then f.getD dx .z else .z) else .z := by
    intro k _
    change ((FPS.const (FPS.const (f.getD k .z)) * CRing.pow (FPS.var : FPS (FPS GF4)) k).coeff dx).coeff dR = _
    rw [FPS.const_mul_coeff, FPS.var_pow_coeff]
    by_cases hk : k = dx
    · subst hk
      simp only [↓reduceIte, CRing.mul_one]
      rfl
    · have hne : dx ≠ k := fun h => hk h.symm
      simp only [hk, hne, ↓reduceIte, CRing.mul_zero]
      rfl
  rw [sumR_congr hterm]
  by_cases hlt : dx < f.length
  · exact sumR_single hlt _
  · have hnone : f[dx]? = none := List.getElem?_eq_none (by omega)
    have hget : f.getD dx .z = .z := by simp [List.getD, hnone]
    have hrhs : (if dR = 0 then f.getD dx .z else .z) = (0 : GF4) := by
      rw [hget]; split <;> rfl
    rw [hrhs]
    exact sumR_eq_zero (fun k hk => by
      have hne : k ≠ dx := by omega
      simp [hne]; rfl)

end FPS2Extract

private theorem sumNat_eq_zero_of_all {n : Nat} {g : Nat → Nat} (h : ∀ k < n, g k = 0) :
    sumNat n g = 0 := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [sumNat_succ, ih (fun k hk => h k (by omega)), h m (Nat.lt_succ_self m)]

private theorem polyAtShiftCoeff_zero_of_ge (poly : List Nat) (b a dR dx : Nat)
    (hge : poly.length ≤ dR + dx) :
    polyAtShiftCoeff poly b a dR dx = 0 := by
  have hz : sumNat poly.length (fun k => poly.getD k 0 * choose k (dR + dx) * b ^ (k - (dR + dx))) = 0 :=
    sumNat_eq_zero_of_all (fun k hk => by
      have hcz : choose k (dR + dx) = 0 := choose_eq_zero_of_lt (by omega)
      simp [hcz])
  simp only [polyAtShiftCoeff, hz, Nat.zero_mul]

private theorem Pass2Prog.execFrom_coeff_zero_of_gt (p : Nat) (prog : List Pass2Instr)
    (D : Nat) (hD : Pass2Prog.maxDeg prog ≤ D) (st : State2)
    (hst : ∀ dR dx, D < dR + dx → st.coeff dR dx = 0) :
    ∀ dR dx, D < dR + dx → (Pass2Prog.execFrom p prog st).coeff dR dx = 0 := by
  induction prog generalizing st with
  | nil => exact hst
  | cons instr rest ih =>
    have hD_rest : Pass2Prog.maxDeg rest ≤ D := by
      cases instr <;> simp only [Pass2Prog.maxDeg] at hD
      · exact Nat.le_trans (Nat.le_max_right _ _) hD
      · exact hD
      · exact hD
      · exact hD
    cases instr with
    | addOut poly =>
      have hpoly : poly.length ≤ D := by
        simp only [Pass2Prog.maxDeg] at hD
        exact Nat.le_trans (Nat.le_max_left _ _) hD
      exact ih hD_rest _ (fun dR dx hgt => by
        simp only [Pass2Instr.exec, hst dR dx hgt, polyAtShiftCoeff_zero_of_ge poly st.b st.a dR dx (by omega)]
        exact Nat.zero_mod p)
    | addWorkConst c =>
      exact ih hD_rest _ hst
    | addInputWork lam =>
      exact ih hD_rest _ hst
    | addInputOut lam =>
      have hD1 : 1 ≤ D := Nat.le_trans (Pass2Prog.maxDeg_pos rest) hD_rest
      exact ih hD_rest _ (fun dR dx hgt => by
        have hcond : ¬ (dR = 0 ∧ dx = 1) := by omega
        simp only [Pass2Instr.exec, hst dR dx hgt, hcond, ↓reduceIte, Nat.add_zero]
        exact Nat.zero_mod p)

theorem Pass2Prog.exec_coeff_zero_of_gt (p : Nat) (prog : List Pass2Instr)
    (dR dx : Nat) (hgt : Pass2Prog.maxDeg prog < dR + dx) :
    (Pass2Prog.exec p prog).coeff dR dx = 0 :=
  Pass2Prog.execFrom_coeff_zero_of_gt p prog (Pass2Prog.maxDeg prog) (Nat.le_refl _)
    ⟨0, 0, fun _ _ => 0⟩ (fun _ _ _ => rfl) dR dx hgt

private theorem sumGF4_eq_z_of_all {n : Nat} {g : Nat → GF4} (h : ∀ k < n, g k = .z) :
    sumGF4 n g = .z := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [sumGF4, ih (fun k hk => h k (by omega)), h m (Nat.lt_succ_self m)]
    rfl

private theorem polyAtShiftCoeffGF4_zero_of_ge (poly : List GF4) (b a : GF4) (dR dx : Nat)
    (hge : poly.length ≤ dR + dx) :
    polyAtShiftCoeffGF4 poly b a dR dx = .z := by
  have hz :
      sumGF4 poly.length (fun k => GF4.mul (poly.getD k .z) (GF4.mul (binomGF4 k (dR + dx)) (GF4.pow b (k - (dR + dx))))) = .z :=
    sumGF4_eq_z_of_all (fun k hk => by
      have hcz : choose k (dR + dx) = 0 := choose_eq_zero_of_lt (by omega)
      have hbg : binomGF4 k (dR + dx) = .z := by simp [binomGF4, hcz]
      rw [hbg]; cases poly.getD k .z <;> rfl)
  simp only [polyAtShiftCoeffGF4, hz]; rfl

private theorem Pass2GF4Prog.execFrom_coeff_zero_of_gt (prog : List Pass2GF4Instr)
    (D : Nat) (hD : Pass2GF4Prog.maxDeg prog ≤ D) (st : State2GF4)
    (hst : ∀ dR dx, D < dR + dx → st.coeff dR dx = .z) :
    ∀ dR dx, D < dR + dx → (Pass2GF4Prog.execFrom prog st).coeff dR dx = .z := by
  induction prog generalizing st with
  | nil => exact hst
  | cons instr rest ih =>
    have hD_rest : Pass2GF4Prog.maxDeg rest ≤ D := by
      cases instr <;> simp only [Pass2GF4Prog.maxDeg] at hD
      · exact Nat.le_trans (Nat.le_max_right _ _) hD
      · exact hD
      · exact hD
      · exact hD
    cases instr with
    | addOut poly =>
      have hpoly : poly.length ≤ D := by
        simp only [Pass2GF4Prog.maxDeg] at hD
        exact Nat.le_trans (Nat.le_max_left _ _) hD
      exact ih hD_rest _ (fun dR dx hgt => by
        simp only [Pass2GF4Instr.exec, hst dR dx hgt, polyAtShiftCoeffGF4_zero_of_ge poly st.b st.a dR dx (by omega)]
        rfl)
    | addWorkConst c =>
      exact ih hD_rest _ hst
    | addInputWork lam =>
      exact ih hD_rest _ hst
    | addInputOut lam =>
      have hD1 : 1 ≤ D := Nat.le_trans (Pass2GF4Prog.maxDeg_pos rest) hD_rest
      exact ih hD_rest _ (fun dR dx hgt => by
        have hcond : ¬ (dR = 0 ∧ dx = 1) := by omega
        simp only [Pass2GF4Instr.exec, hst dR dx hgt, hcond, ↓reduceIte]
        rfl)

theorem Pass2GF4Prog.exec_coeff_zero_of_gt (prog : List Pass2GF4Instr)
    (dR dx : Nat) (hgt : Pass2GF4Prog.maxDeg prog < dR + dx) :
    (Pass2GF4Prog.exec prog).coeff dR dx = .z :=
  Pass2GF4Prog.execFrom_coeff_zero_of_gt prog (Pass2GF4Prog.maxDeg prog) (Nat.le_refl _)
    ⟨.z, .z, fun _ _ => .z⟩ (fun _ _ _ => rfl) dR dx hgt

/--
**Converse Completeness for `T1s`:** if `prog` literally cleanly computes `f` over every
characteristic-`p` commutative ring `R` (instantiated constructively on the formal power series
ring `FPS (FPS (ModP p hp))`), then symbolic `CleanlyComputes2 p prog f` holds.
-/
theorem pass2_ring_exec_implies_clean {p : Nat} (hp : 1 < p)
    {prog : List Pass2Instr} {f : List Nat}
    (hexec : ∀ (R : Type) [CRing R], (CRing.natCast p : R) = 0 →
      ∀ o u x : R, Pass2Prog.execRing x prog (o, u) = (o + evalPolyR f x, u)) :
    CleanlyComputes2 p prog f := by
  let R2 := FPS (FPS (ModP p hp))
  have hchar : (CRing.natCast p : R2) = 0 := by
    rw [FPS.natCast_eq, FPS.natCast_eq, ModP.natCast_p_eq_zero p hp, FPS.const_zero, FPS.const_zero]
  let U : R2 := FPS.const FPS.var
  let X : R2 := FPS.var
  let D := Pass2Prog.maxDeg prog
  have hrun := hexec R2 hchar 0 U X
  rw [Pass2Prog.execRing_eq_evalState2 hchar prog D (Nat.le_refl D) 0 U X] at hrun
  have h1 : evalState2Coeff D (Pass2Prog.exec p prog).coeff U X = evalPolyR f X := by
    have hfst := congrArg Prod.fst hrun
    simpa [CRing.zero_add] using hfst
  have h2 : U + CRing.natCast (Pass2Prog.exec p prog).b + CRing.natCast (Pass2Prog.exec p prog).a * X = U :=
    congrArg Prod.snd hrun
  have h2z : (CRing.natCast (Pass2Prog.exec p prog).b : R2) + CRing.natCast (Pass2Prog.exec p prog).a * X = 0 := by
    apply CRing.add_left_cancel (a := U)
    rw [← CRing.add_assoc, h2, CRing.add_zero]
  have hb : (Pass2Prog.exec p prog).b % p = 0 := by
    have hc := congrArg (fun s : R2 => (s.coeff 0).coeff 0) h2z
    have hcoeff :
        (((CRing.natCast (Pass2Prog.exec p prog).b : R2) +
          CRing.natCast (Pass2Prog.exec p prog).a * X).coeff 0).coeff 0 =
        (CRing.natCast (Pass2Prog.exec p prog).b : ModP p hp) := by
      change ((CRing.natCast (Pass2Prog.exec p prog).b : R2).coeff 0).coeff 0 +
        ((CRing.natCast (Pass2Prog.exec p prog).a * X : R2).coeff 0).coeff 0 = _
      rw [FPS.natCast_eq, FPS.natCast_eq, FPS.natCast_eq, FPS.natCast_eq, FPS.const_mul_coeff]
      have hx0 : (X.coeff 0 : FPS (ModP p hp)) = 0 := rfl
      rw [hx0, CRing.mul_zero]
      change (CRing.natCast (Pass2Prog.exec p prog).b : ModP p hp) + 0 = _
      exact CRing.add_zero _
    rw [hcoeff] at hc
    have hval := congrArg ModP.val hc
    rw [ModP.natCast_val] at hval
    exact hval
  have ha : (Pass2Prog.exec p prog).a % p = 0 := by
    have hc := congrArg (fun s : R2 => (s.coeff 1).coeff 0) h2z
    have hcoeff :
        (((CRing.natCast (Pass2Prog.exec p prog).b : R2) +
          CRing.natCast (Pass2Prog.exec p prog).a * X).coeff 1).coeff 0 =
        (CRing.natCast (Pass2Prog.exec p prog).a : ModP p hp) := by
      change ((CRing.natCast (Pass2Prog.exec p prog).b : R2).coeff 1).coeff 0 +
        ((CRing.natCast (Pass2Prog.exec p prog).a * X : R2).coeff 1).coeff 0 = _
      rw [FPS.natCast_eq, FPS.natCast_eq, FPS.natCast_eq, FPS.natCast_eq, FPS.const_mul_coeff]
      have hx1 : (X.coeff 1 : FPS (ModP p hp)) = 1 := rfl
      rw [hx1, CRing.mul_one]
      change (0 : ModP p hp) + CRing.natCast (Pass2Prog.exec p prog).a = _
      exact CRing.zero_add _
    rw [hcoeff] at hc
    have hval := congrArg ModP.val hc
    rw [ModP.natCast_val] at hval
    exact hval
  refine ⟨hb, ha, fun dR dx => ?_⟩
  have hce := congrArg (fun s : R2 => (s.coeff dx).coeff dR) h1
  rw [evalState2Coeff_fps2_coeff, evalPolyR_fps2_coeff] at hce
  by_cases hle : dR + dx ≤ D
  · simp only [hle, ↓reduceIte] at hce
    have hval := congrArg ModP.val hce
    rw [ModP.natCast_val] at hval
    by_cases hdR : dR = 0
    · simp only [hdR, ↓reduceIte] at hval ⊢
      rw [ModP.natCast_val] at hval
      exact hval
    · simp only [hdR, ↓reduceIte] at hval ⊢
      exact hval.trans (Nat.zero_mod p).symm
  · have hgt : D < dR + dx := by omega
    simp only [hle, ↓reduceIte] at hce
    rw [Pass2Prog.exec_coeff_zero_of_gt p prog dR dx hgt, Nat.zero_mod]
    have hval := congrArg ModP.val hce
    by_cases hdR : dR = 0
    · simp only [hdR, ↓reduceIte] at hval ⊢
      rw [ModP.natCast_val] at hval
      exact hval
    · simp only [hdR, ↓reduceIte, Nat.zero_mod]

/--
**Theorem `T1sc` (Exact Bi-Directional Equivalence for `Pass2Prog`):**
For every modulus `p > 1`, symbolic formal-polynomial cleanliness `CleanlyComputes2 p prog f`
holds **if and only if** literal ring execution `Pass2Prog.execRing` cleanly computes `f` over
every commutative ring `R` of characteristic `p`.
-/
theorem pass2_clean_iff_ring_exec {p : Nat} (hp : 1 < p)
    (prog : List Pass2Instr) (f : List Nat) :
    CleanlyComputes2 p prog f ↔
      ∀ (R : Type) [CRing R], (CRing.natCast p : R) = 0 →
        ∀ o u x : R, Pass2Prog.execRing x prog (o, u) = (o + evalPolyR f x, u) :=
  ⟨pass2_clean_implies_ring_exec, pass2_ring_exec_implies_clean hp⟩

/--
**Direct Literal-Ring Theorem `T1` (`rp_pass_two_literal_ring_iff`):**
Eliminates all symbolic intermediate definitions (`State2`, `polyAtShiftCoeff`, `CleanlyComputes2`)
from the statement of Theorem `T1`: over prime `p`, a polynomial `f` is cleanly computed by a
`≤ t`-access passive 2-register program under literal ring execution `Pass2Prog.execRing` across
all characteristic-`p` commutative rings iff every degree `d ≥ 2` with `f[d] ≢ 0 (mod p)` satisfies
`s_p(d) ≤ min (p - 1) (t - 1)`.
-/
theorem rp_pass_two_literal_ring_iff (p t : Nat) (hp : IsPrime p) (ht : 1 ≤ t) (f : List Nat) :
    (∃ prog : List Pass2Instr, Pass2Prog.accesses prog ≤ t ∧
      ∀ (R : Type) [CRing R], (CRing.natCast p : R) = 0 →
        ∀ o u x : R, Pass2Prog.execRing x prog (o, u) = (o + evalPolyR f x, u)) ↔
      ∀ d : Nat, 2 ≤ d → f.getD d 0 % p ≠ 0 →
        digitSum p d ≤ min (p - 1) (t - 1) := by
  have hp1 : 1 < p := by have := hp.1; omega
  have hEq :
      (∃ prog : List Pass2Instr, Pass2Prog.accesses prog ≤ t ∧
        ∀ (R : Type) [CRing R], (CRing.natCast p : R) = 0 →
          ∀ o u x : R, Pass2Prog.execRing x prog (o, u) = (o + evalPolyR f x, u)) ↔
      InRPPass2 p t f := by
    constructor
    · rintro ⟨prog, hacc, hexec⟩
      exact ⟨prog, hacc, (pass2_clean_iff_ring_exec hp1 prog f).2 hexec⟩
    · rintro ⟨prog, hacc, hclean⟩
      exact ⟨prog, hacc, (pass2_clean_iff_ring_exec hp1 prog f).1 hclean⟩
  exact hEq.trans (rp_pass_two_iff p t hp ht f)

/--
**Converse Completeness for `T1es`:** if `prog` literally cleanly computes `f` over every
commutative `GF4`-algebra `(R, φ)` (instantiated constructively on `FPS (FPS GF4)`),
then symbolic `CleanlyComputes2GF4 prog f` holds.
-/
theorem pass2gf4_alg_exec_implies_clean {prog : List Pass2GF4Instr} {f : List GF4}
    (hexec : ∀ (R : Type) [CRing R] (φ : GF4Hom R) (o u x : R),
      Pass2GF4Prog.execAlg φ x prog (o, u) = (o + evalPolyGF4Alg φ f x, u)) :
    CleanlyComputes2GF4 prog f := by
  let R2 := FPS (FPS GF4)
  let φ2 : GF4Hom R2 := FPS.constGF4Hom (FPS.constGF4Hom GF4Hom.id)
  let U : R2 := FPS.const FPS.var
  let X : R2 := FPS.var
  let D := Pass2GF4Prog.maxDeg prog
  have hrun := hexec R2 φ2 0 U X
  rw [Pass2GF4Prog.execAlg_eq_evalState2GF4 φ2 prog D (Nat.le_refl D) 0 U X] at hrun
  have h1 : evalState2GF4Coeff φ2 D (Pass2GF4Prog.exec prog).coeff U X = evalPolyGF4Alg φ2 f X := by
    have hfst := congrArg Prod.fst hrun
    simpa [CRing.zero_add] using hfst
  have h2 : U + φ2.toFun (Pass2GF4Prog.exec prog).b + φ2.toFun (Pass2GF4Prog.exec prog).a * X = U :=
    congrArg Prod.snd hrun
  have h2z : φ2.toFun (Pass2GF4Prog.exec prog).b + φ2.toFun (Pass2GF4Prog.exec prog).a * X = 0 := by
    apply CRing.add_left_cancel (a := U)
    rw [← CRing.add_assoc, h2, CRing.add_zero]
  have hb : (Pass2GF4Prog.exec prog).b = .z := by
    have hc := congrArg (fun s : R2 => (s.coeff 0).coeff 0) h2z
    have hcoeff :
        ((φ2.toFun (Pass2GF4Prog.exec prog).b + φ2.toFun (Pass2GF4Prog.exec prog).a * X).coeff 0).coeff 0 =
        (Pass2GF4Prog.exec prog).b := by
      change (FPS.const (FPS.const (Pass2GF4Prog.exec prog).b) |>.coeff 0).coeff 0 +
        ((FPS.const (FPS.const (Pass2GF4Prog.exec prog).a) * X).coeff 0).coeff 0 = _
      rw [FPS.const_mul_coeff]
      have hx0 : (X.coeff 0 : FPS GF4) = 0 := rfl
      rw [hx0, CRing.mul_zero]
      change (Pass2GF4Prog.exec prog).b + (0 : GF4) = _
      exact CRing.add_zero _
    rw [hcoeff] at hc
    exact hc
  have ha : (Pass2GF4Prog.exec prog).a = .z := by
    have hc := congrArg (fun s : R2 => (s.coeff 1).coeff 0) h2z
    have hcoeff :
        ((φ2.toFun (Pass2GF4Prog.exec prog).b + φ2.toFun (Pass2GF4Prog.exec prog).a * X).coeff 1).coeff 0 =
        (Pass2GF4Prog.exec prog).a := by
      change (FPS.const (FPS.const (Pass2GF4Prog.exec prog).b) |>.coeff 1).coeff 0 +
        ((FPS.const (FPS.const (Pass2GF4Prog.exec prog).a) * X).coeff 1).coeff 0 = _
      rw [FPS.const_mul_coeff]
      have hx1 : (X.coeff 1 : FPS GF4) = 1 := rfl
      rw [hx1, CRing.mul_one]
      change (0 : GF4) + (Pass2GF4Prog.exec prog).a = _
      exact CRing.zero_add _
    rw [hcoeff] at hc
    exact hc
  refine ⟨hb, ha, fun dR dx => ?_⟩
  have hce := congrArg (fun s : R2 => (s.coeff dx).coeff dR) h1
  rw [evalState2GF4Coeff_fps2_coeff, evalPolyGF4Alg_fps2_coeff] at hce
  by_cases hle : dR + dx ≤ D
  · simp only [hle, ↓reduceIte] at hce
    exact hce
  · have hgt : D < dR + dx := by omega
    simp only [hle, ↓reduceIte] at hce
    rw [Pass2GF4Prog.exec_coeff_zero_of_gt prog dR dx hgt]
    exact hce

/--
**Theorem `T1esc` (Exact Bi-Directional Equivalence for `Pass2GF4Prog`):**
Symbolic formal-polynomial cleanliness `CleanlyComputes2GF4 prog f` holds **if and only if**
literal `GF4`-algebra execution `Pass2GF4Prog.execAlg` cleanly computes `f` over every
commutative `GF4`-algebra `(R, φ)`.
-/
theorem pass2gf4_clean_iff_alg_exec (prog : List Pass2GF4Instr) (f : List GF4) :
    CleanlyComputes2GF4 prog f ↔
      ∀ (R : Type) [CRing R] (φ : GF4Hom R) (o u x : R),
        Pass2GF4Prog.execAlg φ x prog (o, u) = (o + evalPolyGF4Alg φ f x, u) :=
  ⟨pass2gf4_clean_implies_alg_exec, pass2gf4_alg_exec_implies_clean⟩

end

end Catalytic
