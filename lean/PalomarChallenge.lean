module
-- SPDX-License-Identifier: Apache-2.0
/-!
# Palomar Challenge Specification (`catalytic-register-frontiers`)
Self-contained Lean 4.35 core statement contract for Palomar Registry (`lake comparator`).
All proofs live in `PalomarSolution.lean` and `Catalytic.*` with zero `sorry`.
-/
namespace Catalytic.Palomar
@[expose] public section
universe u

class CRing (R : Type u) extends Add R, Mul R, Neg R, Zero R, One R where
  add_assoc : ∀ a b c : R, (a + b) + c = a + (b + c)
  add_comm : ∀ a b : R, a + b = b + a
  zero_add : ∀ a : R, 0 + a = a
  add_neg : ∀ a : R, a + (-a) = 0
  mul_assoc : ∀ a b c : R, (a * b) * c = a * (b * c)
  mul_comm : ∀ a b : R, a * b = b * a
  one_mul : ∀ a : R, 1 * a = a
  left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
def CRing.natCast {R : Type u} [CRing R] : Nat → R
  | 0 => 0 | n + 1 => CRing.natCast n + 1
def CRing.intCast {R : Type u} [CRing R] : Int → R
  | Int.ofNat n => CRing.natCast n | Int.negSucc n => -(CRing.natCast (n + 1))
def CRing.pow {R : Type u} [CRing R] (a : R) : Nat → R
  | 0 => 1 | n + 1 => CRing.pow a n * a
class Char2CRing (R : Type u) extends CRing R where
  add_self : ∀ a : R, a + a = 0

def IsPrime (p : Nat) : Prop := 2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p
def fact : Nat → Nat | 0 => 1 | n + 1 => (n + 1) * fact n
def choose : Nat → Nat → Nat
  | _, 0 => 1 | 0, _ + 1 => 0 | n + 1, k + 1 => choose n k + choose n (k + 1)
def sumNat (n : Nat) (f : Nat → Nat) : Nat :=
  match n with | 0 => 0 | m + 1 => sumNat m f + f m
def digitSumFuel (p : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n =>
    if 2 ≤ p then (if n = 0 then 0 else n % p + digitSumFuel p fuel (n / p)) else n
def digitSum (p n : Nat) : Nat := digitSumFuel p (n + 1) n
def baseDigitsFuel (δ : Nat) : Nat → Nat → List Nat
  | 0, N => [N]
  | fuel + 1, N => if N < δ then [N] else (N % δ) :: baseDigitsFuel δ fuel (N / δ)
def baseDigits (δ N : Nat) : List Nat := baseDigitsFuel δ (N + 1) N

-- Two-register passive programs over `𝔽_p` (Vinciguerra Def. 2.2)
inductive Pass2Instr where
  | addOut (poly : List Nat) | addWorkConst (c : Nat)
  | addInputOut (lam : Nat)  | addInputWork (lam : Nat)
def Pass2Prog.accesses : List Pass2Instr → Nat
  | [] => 0
  | .addOut _ :: rest | .addWorkConst _ :: rest => Pass2Prog.accesses rest
  | .addInputOut _ :: rest | .addInputWork _ :: rest => 1 + Pass2Prog.accesses rest
def polyAtShiftCoeff (poly : List Nat) (b a dR dx : Nat) : Nat :=
  let d := dR + dx
  (sumNat poly.length (fun k => poly.getD k 0 * choose k d * b ^ (k - d))) * (choose d dx * a ^ dx)
structure State2 where
  b : Nat
  a : Nat
  coeff : Nat → Nat → Nat
def Pass2Instr.exec (p : Nat) (st : State2) : Pass2Instr → State2
  | .addOut poly =>
    { st with coeff := fun dR dx => (st.coeff dR dx + polyAtShiftCoeff poly st.b st.a dR dx) % p }
  | .addWorkConst c => { st with b := (st.b + c) % p }
  | .addInputOut lam =>
    { st with coeff := fun dR dx => (st.coeff dR dx + if dR = 0 ∧ dx = 1 then lam else 0) % p }
  | .addInputWork lam => { st with a := (st.a + lam) % p }
def Pass2Prog.execFrom (p : Nat) : List Pass2Instr → State2 → State2
  | [], st => st | i :: rest, st => Pass2Prog.execFrom p rest (i.exec p st)
def Pass2Prog.exec (p : Nat) (prog : List Pass2Instr) : State2 :=
  Pass2Prog.execFrom p prog ⟨0, 0, fun _ _ => 0⟩
def CleanlyComputes2 (p : Nat) (prog : List Pass2Instr) (f : List Nat) : Prop :=
  let st := Pass2Prog.exec p prog
  st.b % p = 0 ∧ st.a % p = 0 ∧
  ∀ dR dx : Nat, st.coeff dR dx % p = (if dR = 0 then f.getD dx 0 else 0) % p
def InRPPass2 (p t : Nat) (f : List Nat) : Prop :=
  ∃ prog : List Pass2Instr, Pass2Prog.accesses prog ≤ t ∧ CleanlyComputes2 p prog f
def monomial (d : Nat) : List Nat := List.replicate d 0 ++ [1]
def sumR {R : Type u} [CRing R] : Nat → (Nat → R) → R
  | 0, _ => 0 | n + 1, f => sumR n f + f n
def evalPolyR {R : Type u} [CRing R] (poly : List Nat) (t : R) : R :=
  sumR poly.length (fun k => CRing.natCast (poly.getD k 0) * CRing.pow t k)
def Pass2Instr.execRing {R : Type u} [CRing R] (x : R) : R × R → Pass2Instr → R × R
  | (o, r), .addOut poly      => (o + evalPolyR poly r, r)
  | (o, r), .addWorkConst c   => (o, r + CRing.natCast c)
  | (o, r), .addInputOut lam  => (o + CRing.natCast lam * x, r)
  | (o, r), .addInputWork lam => (o, r + CRing.natCast lam * x)
def Pass2Prog.execRing {R : Type u} [CRing R] (x : R) : List Pass2Instr → R × R → R × R
  | [], st => st | i :: rest, st => Pass2Prog.execRing x rest (i.execRing x st)

-- Strictly bilinear passive programs (`T2`)
inductive BilinInstr (n : Nat) where
  | mulAdd (dst a b : Fin n) | addInput (dst : Fin n)
def BilinProg.accesses {n : Nat} : List (BilinInstr n) → Nat
  | [] => 0 | .mulAdd _ _ _ :: rest => BilinProg.accesses rest | .addInput _ :: rest => 1 + BilinProg.accesses rest
def BilinProg.bilinOps {n : Nat} : List (BilinInstr n) → Nat
  | [] => 0 | .mulAdd _ _ _ :: rest => 1 + BilinProg.bilinOps rest | .addInput _ :: rest => BilinProg.bilinOps rest
def BilinInstr.isValidPassive {n : Nat} : BilinInstr n → Prop
  | .mulAdd dst a b => dst ≠ a ∧ dst ≠ b ∧ a.val ≠ 0 ∧ b.val ≠ 0 | .addInput _ => True
def BilinInstr.exec {n : Nat} {R : Type u} [CRing R] (x : R) (st : Fin n → R) :
    BilinInstr n → (Fin n → R)
  | .mulAdd dst a b => fun i => if i = dst then st dst + st a * st b else st i
  | .addInput dst   => fun i => if i = dst then st dst + x else st i
def BilinProg.exec {n : Nat} {R : Type u} [CRing R] (x : R) :
    List (BilinInstr n) → (Fin n → R) → (Fin n → R)
  | [], st => st | instr :: rest, st => BilinProg.exec x rest (instr.exec x st)

-- Three- and four-register passive powering and streaming (`T3a`–`T3i`)
inductive Pass3InstrR (R : Type u) where
  | addOut (terms : List (Nat × Nat × R)) | addWorkV (coeff : R) (deg : Nat) | addInputU (alpha : R)
def Pass3Prog.accesses {R : Type u} : List (Pass3InstrR R) → Nat
  | [] => 0
  | .addOut _ :: rest | .addWorkV _ _ :: rest => Pass3Prog.accesses rest
  | .addInputU _ :: rest => 1 + Pass3Prog.accesses rest
def evalBivar {R : Type u} [CRing R] (u v : R) : List (Nat × Nat × R) → R
  | [] => 0 | (a, b, c) :: rest => c * (CRing.pow u a * CRing.pow v b) + evalBivar u v rest
def Pass3InstrR.exec {R : Type u} [CRing R] (x : R) (st : R × R × R) : Pass3InstrR R → R × R × R
  | .addOut terms => (st.1 + evalBivar st.2.1 st.2.2 terms, st.2.1, st.2.2)
  | .addWorkV c d => (st.1, st.2.1, st.2.2 + c * CRing.pow st.2.1 d)
  | .addInputU α  => (st.1, st.2.1 + α * x, st.2.2)
def Pass3Prog.exec {R : Type u} [CRing R] (x : R) : List (Pass3InstrR R) → (R × R × R) → (R × R × R)
  | [], st => st | i :: rest, st => Pass3Prog.exec x rest (i.exec x st)
inductive Work3Instr (R : Type u) where
  | addX (dst : Fin 3) (c : R) | addPoly (dst : Fin 3) (terms : List (Nat × Nat × R))
def Work3Prog.accesses {R : Type u} : List (Work3Instr R) → Nat
  | [] => 0 | .addX _ _ :: rest => 1 + Work3Prog.accesses rest | .addPoly _ _ :: rest => Work3Prog.accesses rest
def Work3Instr.exec {R : Type u} [CRing R] (x : R) (st : R × R × R) : Work3Instr R → R × R × R
  | .addX dst c => match dst.val with
    | 0 => (st.1 + c * x, st.2.1, st.2.2) | 1 => (st.1, st.2.1 + c * x, st.2.2) | _ => (st.1, st.2.1, st.2.2 + c * x)
  | .addPoly dst terms => match dst.val with
    | 0 => (st.1 + evalBivar st.2.1 st.2.2 terms, st.2.1, st.2.2)
    | 1 => (st.1, st.2.1 + evalBivar st.2.2 st.1 terms, st.2.2)
    | _ => (st.1, st.2.1, st.2.2 + evalBivar st.1 st.2.1 terms)
inductive Pass4Instr (R : Type u) where
  | work (w : Work3Instr R) | outAddPow (coeff : R) (deg : Nat)
def Pass4Prog.accesses {R : Type u} : List (Pass4Instr R) → Nat
  | [] => 0
  | .work w :: rest => Work3Prog.accesses [w] + Pass4Prog.accesses rest
  | .outAddPow _ _ :: rest => Pass4Prog.accesses rest
def Pass4Instr.exec {R : Type u} [CRing R] (x : R) (st : R × R × R × R) : Pass4Instr R → R × R × R × R
  | .work w => let w' := w.exec x st.2; (st.1, w'.1, w'.2.1, w'.2.2)
  | .outAddPow coeff d => (st.1 + coeff * CRing.pow st.2.1 d, st.2.1, st.2.2.1, st.2.2.2)
def Pass4Prog.exec {R : Type u} [CRing R] (x : R) : List (Pass4Instr R) → (R × R × R × R) → (R × R × R × R)
  | [], st => st | i :: rest, st => Pass4Prog.exec x rest (i.exec x st)
instance instCRingFinFun {n : Nat} {R : Type u} [CRing R] : CRing (Fin n → R) where
  zero := fun _ => 0
  one := fun _ => 1
  add f g i := f i + g i
  mul f g i := f i * g i
  neg f i := -(f i)
  add_assoc a b c := funext fun i => CRing.add_assoc (a i) (b i) (c i)
  add_comm a b := funext fun i => CRing.add_comm (a i) (b i)
  zero_add a := funext fun i => CRing.zero_add (a i)
  add_neg a := funext fun i => CRing.add_neg (a i)
  mul_assoc a b c := funext fun i => CRing.mul_assoc (a i) (b i) (c i)
  mul_comm a b := funext fun i => CRing.mul_comm (a i) (b i)
  one_mul a := funext fun i => CRing.one_mul (a i)
  left_distrib a b c := funext fun i => CRing.left_distrib (a i) (b i) (c i)
def sumFin {n : Nat} {R : Type u} [CRing R] (v : Fin n → R) : R :=
  sumR n (fun j => if h : j < n then v ⟨j, h⟩ else 0)

-- Balanced zero-workspace bilinear product (`T4`)
inductive CatOp where
  | addInput (dst : Nat) (sign : Int) (varIdx : Nat) | addProd (dst a b : Nat) (sign : Int)
def CatOp.isStrictValid : CatOp → Prop
  | .addInput _ s _ => s = 1 ∨ s = -1
  | .addProd dst a b s => (s = 1 ∨ s = -1) ∧ dst ≠ a ∧ dst ≠ b ∧ a ≠ b
def CatOp.usesOnly (regs : List Nat) : CatOp → Prop
  | .addInput dst _ _ => dst ∈ regs
  | .addProd dst a b _ => dst ∈ regs ∧ a ∈ regs ∧ b ∈ regs
def CatOp.exec {R : Type u} [CRing R] (xs : Nat → R) (st : Nat → R) : CatOp → (Nat → R)
  | .addInput dst s v  => fun r => if r = dst then st dst + CRing.intCast s * xs v else st r
  | .addProd dst a b s => fun r => if r = dst then st dst + CRing.intCast s * (st a * st b) else st r
def CatProg.exec {R : Type u} [CRing R] (xs : Nat → R) : List CatOp → (Nat → R) → (Nat → R)
  | [], st => st | op :: rest, st => CatProg.exec xs rest (op.exec xs st)
def rangeProd {R : Type u} [CRing R] (xs : Nat → R) (offset : Nat) : Nat → R
  | 0 => 1 | n + 1 => rangeProd xs offset n * xs (offset + n)

/-! ## 7. Headline Challenge Theorems (`T1`–`T4` and Corollaries) -/
/-- T1: Exact base-`p` digit-sum dichotomy for `RP^{pass}_{𝔽_p}(2, t)`. -/
theorem t1_digit_sum_dichotomy :
    ∀ (p t : Nat), IsPrime p → 1 ≤ t → ∀ (f : List Nat),
      InRPPass2 p t f ↔ ∀ d : Nat, 2 ≤ d → f.getD d 0 % p ≠ 0 → digitSum p d ≤ min (p - 1) (t - 1) := by sorry
/-- T1a: 2-access Frobenius collapse `x^(p^m) ∈ RP^{pass}_{𝔽_p}(2, 2)`. -/
theorem t1a_two_access_frobenius_collapse :
    ∀ (p m : Nat), IsPrime p → InRPPass2 p 2 (monomial (p ^ m)) := by sorry
/-- T1b: Over `𝔽_2`, `x^3 ∉ RP^{pass}_{𝔽_2}(2, t)` for all `t`. -/
theorem t1b_f2_saturation : ∀ (t : Nat), ¬ InRPPass2 2 t (monomial 3) := by sorry
/-- T1c: Impossibility threshold whenever `s_p(d) ≥ p` and `d ≥ 2`. -/
theorem t1c_impossibility_threshold :
    ∀ (p d t : Nat), IsPrime p → 2 ≤ d → 1 ≤ t → p ≤ digitSum p d → ¬ InRPPass2 p t (monomial d) := by sorry
/-- T1d: Large-characteristic analogue of Vinciguerra Theorem 3.5 for `2 ≤ d < p`. -/
theorem t1d_vinciguerra_recovery :
    ∀ (p d t : Nat), IsPrime p → 2 ≤ d → d < p → 1 ≤ t → (InRPPass2 p t (monomial d) ↔ d + 1 ≤ t) := by sorry
/-- T1s: Literal `CRing` soundness bridge for every characteristic-`p` ring `R`. -/
theorem t1s_pass2_ring_soundness :
    ∀ (p : Nat) (prog : List Pass2Instr) (f : List Nat), CleanlyComputes2 p prog f →
      ∀ (R : Type) [CRing R], (CRing.natCast p : R) = 0 →
        ∀ o u x : R, Pass2Prog.execRing x prog (o, u) = (o + evalPolyR f x, u) := by sorry
/-- T2: Strictly bilinear 2-access Frobenius collapse over any `Char2CRing R`. -/
theorem t2_bilinear_frobenius_collapse :
    ∀ (k : Nat), 1 ≤ k →
      ∃ prog : List (BilinInstr (k + 1)),
        BilinProg.accesses prog = 2 ∧ BilinProg.bilinOps prog = 4 * k - 2 ∧
        (∀ instr ∈ prog, instr.isValidPassive) ∧
        ∀ (R : Type) [Char2CRing R] (x : R) (init : Fin (k + 1) → R),
          let final := BilinProg.exec x prog init
          final ⟨0, Nat.zero_lt_succ k⟩ = init ⟨0, Nat.zero_lt_succ k⟩ + CRing.pow x (2 ^ k) ∧
          ∀ i : Fin (k + 1), i.val ≠ 0 → final i = init i := by sorry
/-- T3a: `x^7 ∈ RP^{pass}_R(3, 5)` whenever `576` is invertible. -/
theorem t3a_three_reg_5call_x7 :
    ∀ (R : Type) [CRing R] (inv576 : R), inv576 * CRing.intCast 576 = 1 →
      ∃ prog : List (Pass3InstrR R), Pass3Prog.accesses prog = 5 ∧
        ∀ x o u v : R, Pass3Prog.exec x prog (o, u, v) = (o + CRing.pow x 7, u, v) := by sorry
/-- T3b: `x^9 ∈ RP^{pass}_R(3, 6)` whenever `382500000` is invertible. -/
theorem t3b_three_reg_6call_x9 :
    ∀ (R : Type) [CRing R] (invD : R), invD * CRing.intCast 382500000 = 1 →
      ∃ prog : List (Pass3InstrR R), Pass3Prog.accesses prog = 6 ∧
        ∀ x o u v : R, Pass3Prog.exec x prog (o, u, v) = (o + CRing.pow x 9, u, v) := by sorry
/-- T3c: `x^11 ∈ RP^{pass}_R(3, 7)` over `ℚ` and good primes. -/
theorem t3c_three_reg_7call_x11 :
    ∀ (R : Type) [CRing R] (invD : R), invD * CRing.intCast 68724637549388656012800 = 1 →
      ∃ prog : List (Pass3InstrR R), Pass3Prog.accesses prog = 7 ∧
        ∀ x o u v : R, Pass3Prog.exec x prog (o, u, v) = (o + CRing.pow x 11, u, v) := by sorry
/-- T3d: `x^13 ∈ RP^{pass}_R(3, 8)` (smallest constructed 3-register exponent `log_13 8 ≈ 0.810714`). -/
theorem t3d_three_reg_8call_x13 :
    ∀ (R : Type) [CRing R] (invD : R), invD * CRing.intCast 2656207148788801777680 = 1 →
      ∃ prog : List (Pass3InstrR R), Pass3Prog.accesses prog = 8 ∧
        ∀ x o u v : R, Pass3Prog.exec x prog (o, u, v) = (o + CRing.pow x 13, u, v) := by sorry
/-- T3e: Exact rational separation of the strictly decreasing exponent chain. -/
theorem t3e_exponent_chain :
    (8 ^ 37 < 13 ^ 30) ∧ (11 ^ 30 < 7 ^ 37) ∧ (7 ^ 16 < 11 ^ 13) ∧ (9 ^ 13 < 6 ^ 16) ∧
    (6 ^ 11 < 9 ^ 9) ∧ (7 ^ 9 < 5 ^ 11) ∧ (5 ^ 6 < 7 ^ 5) ∧ (5 ^ 5 < 4 ^ 6) ∧ (15 ^ 30 < 9 ^ 37) := by sorry
/-- T3f: Unique integer minimizer `t = 8` of `log_{2t - 3} t` for `t ≥ 4` (integer inequality). -/
theorem t3f_global_integer_optimality :
    (8 ^ 37 < 13 ^ 30) ∧ (∀ t : Nat, 4 ≤ t → t ≠ 8 → (2 * t - 3) ^ 30 < t ^ 37) := by sorry
/-- T3g: `x^15 ∈ RP^{pass}_R(3, 9)` (post-minimum ascent point `log_15 9 ≈ 0.811368`). -/
theorem t3g_three_reg_9call_x15 :
    ∀ (R : Type) [CRing R] (invD : R),
      invD * CRing.intCast 876702103804656272895371895753963647960420947968000 = 1 →
      ∃ prog : List (Pass3InstrR R), Pass3Prog.accesses prog = 9 ∧
        ∀ x o u v : R, Pass3Prog.exec x prog (o, u, v) = (o + CRing.pow x 15, u, v) := by sorry
/-- T3h: Four-register passive powering for `N ≥ 1` under stated invertibility hypotheses. -/
theorem t3h_four_reg_powering :
    (∀ (R : Type) [CRing R] (N : Nat), 1 ≤ N →
      ∀ (invD8 invFact12 invFactLen : R),
      invD8 * CRing.intCast 2656207148788801777680 = 1 →
      invFact12 * CRing.natCast (fact 12) = 1 →
      invFactLen * CRing.natCast (fact (baseDigits 13 N).length) = 1 →
      ∃ prog : List (Pass4Instr R), let ℓ := (baseDigits 13 N).length - 1
        13 ^ ℓ ≤ N ∧ 3 * Pass4Prog.accesses prog < 104 * 8 ^ ℓ ∧
        ∀ x o u r1 r2 : R, Pass4Prog.exec x prog (o, u, r1, r2) = (o + CRing.pow x N, u, r1, r2)) ∧
    (∀ (R : Type) [CRing R] (N : Nat), 1 ≤ N →
      ∀ (invFact6 invFactLen : R),
      invFact6 * CRing.natCast (fact 6) = 1 →
      invFactLen * CRing.natCast (fact (baseDigits 7 N).length) = 1 →
      ∃ prog : List (Pass4Instr R), let ℓ := (baseDigits 7 N).length - 1
        7 ^ ℓ ≤ N ∧ 3 * Pass4Prog.accesses prog < 70 * 5 ^ ℓ ∧
        ∀ x o u r1 r2 : R, Pass4Prog.exec x prog (o, u, r1, r2) = (o + CRing.pow x N, u, r1, r2)) := by sorry
/-- T3i: Coordinatewise four-register powering bound over `R^n` (product-ring corollary of `T3h`). -/
theorem t3i_streaming_frequency_moment :
    ∀ (R : Type) [CRing R] (n D : Nat), 1 ≤ D →
      ∀ (invD8 invFact12 invFactLen : R),
      invD8 * CRing.intCast 2656207148788801777680 = 1 →
      invFact12 * CRing.natCast (fact 12) = 1 →
      invFactLen * CRing.natCast (fact (baseDigits 13 D).length) = 1 →
      ∃ prog : List (Pass4Instr (Fin n → R)), let ℓ := (baseDigits 13 D).length - 1
        13 ^ ℓ ≤ D ∧ 3 * Pass4Prog.accesses prog < 104 * 8 ^ ℓ ∧
        ∀ f o u r1 r2 : Fin n → R, let res := Pass4Prog.exec f prog (o, u, r1, r2)
          (∀ i : Fin n, res.1 i = o i + CRing.pow (f i) D) ∧ res.2 = (u, r1, r2) ∧
          sumFin res.1 = sumFin o + sumFin (fun i => CRing.pow (f i) D) := by sorry
/-- T4: Balanced zero-workspace bilinear multilinear product on `≤ k + 2` designated registers. -/
theorem t4_balanced_multilinear_product :
    ∀ (k target : Nat) (sign : Int) (pool : List Nat) (offset : Nat),
      (sign = 1 ∨ sign = -1) → (k = 0 ∨ k + 1 ≤ pool.length) → (target :: pool).Nodup →
      let regs := if k = 0 then [target] else target :: pool.take (k + 1)
      ∃ prog : List CatOp, 3 * prog.length + 4 = 7 * (2 ^ k) ^ 2 ∧ regs.length ≤ k + 2 ∧
        (∀ op ∈ prog, op.isStrictValid ∧ op.usesOnly regs) ∧
        ∀ (R : Type) [CRing R] (xs st : Nat → R), CatProg.exec xs prog st =
          (fun r => if r = target then st target + CRing.intCast sign * rangeProd xs offset (2 ^ k) else st r) := by sorry

end
end Catalytic.Palomar
