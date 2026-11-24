module
-- SPDX-License-Identifier: Apache-2.0

public import Catalytic
public import Solution
import all Catalytic.BilinearFrobenius
import all Catalytic.BalancedProduct

/-!
# Palomar Comparator Solution (`catalytic-register-frontiers`)

Complete kernel-checked implementation of all 17 Palomar Registry Comparator theorems,
discharged directly from the verified `Catalytic.*` and `Solution` proof library.
The definition block below matches the standalone Comparator specification verbatim.
-/

namespace Catalytic.Palomar

@[expose] public section

universe u

/-! ## 1. Commutative Rings (`CRing`, `Char2CRing`) -/

/-- Minimal commutative ring with `1` (zero Mathlib). -/
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
  | 0 => 0
  | n + 1 => CRing.natCast n + 1

def CRing.intCast {R : Type u} [CRing R] : Int → R
  | Int.ofNat n => CRing.natCast n
  | Int.negSucc n => -(CRing.natCast (n + 1))

def CRing.pow {R : Type u} [CRing R] (a : R) : Nat → R
  | 0 => 1
  | n + 1 => CRing.pow a n * a

/-- Characteristic-2 commutative ring (`a + a = 0`). -/
class Char2CRing (R : Type u) extends CRing R where
  add_self : ∀ a : R, a + a = 0

/-! ## 2. Elementary Number Theory (Structural Recursion, Zero External Imports) -/

def IsPrime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

def choose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)

def sumNat (n : Nat) (f : Nat → Nat) : Nat :=
  match n with
  | 0 => 0
  | m + 1 => sumNat m f + f m

def digitSumFuel (p : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n =>
    if 2 ≤ p then
      if n = 0 then 0 else n % p + digitSumFuel p fuel (n / p)
    else n

/-- Exact base-`p` digit sum `s_p(n)` (fuel `n + 1` suffices for all `p ≥ 2`). -/
def digitSum (p n : Nat) : Nat :=
  digitSumFuel p (n + 1) n

def baseDigitsFuel (δ : Nat) : Nat → Nat → List Nat
  | 0, N => [N]
  | fuel + 1, N =>
    if N < δ then [N]
    else (N % δ) :: baseDigitsFuel δ fuel (N / δ)

/-- LSB-first base-`δ` digit expansion of `N` (`δ ≥ 2`). -/
def baseDigits (δ N : Nat) : List Nat :=
  baseDigitsFuel δ (N + 1) N

/-! ## 3. Two-Register Passive Programs over `𝔽_p` (Vinciguerra Def. 2.2) -/

inductive Pass2Instr where
  | addOut (poly : List Nat) : Pass2Instr
  | addWorkConst (c : Nat) : Pass2Instr
  | addInputOut (lam : Nat) : Pass2Instr
  | addInputWork (lam : Nat) : Pass2Instr

def Pass2Prog.accesses : List Pass2Instr → Nat
  | [] => 0
  | .addOut _ :: rest => Pass2Prog.accesses rest
  | .addWorkConst _ :: rest => Pass2Prog.accesses rest
  | .addInputOut _ :: rest => 1 + Pass2Prog.accesses rest
  | .addInputWork _ :: rest => 1 + Pass2Prog.accesses rest

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
  | .addWorkConst c =>
    { st with b := (st.b + c) % p }
  | .addInputOut lam =>
    { st with coeff := fun dR dx => (st.coeff dR dx + if dR = 0 ∧ dx = 1 then lam else 0) % p }
  | .addInputWork lam =>
    { st with a := (st.a + lam) % p }

def Pass2Prog.execFrom (p : Nat) : List Pass2Instr → State2 → State2
  | [], st => st
  | i :: rest, st => Pass2Prog.execFrom p rest (i.exec p st)

def Pass2Prog.exec (p : Nat) (prog : List Pass2Instr) : State2 :=
  Pass2Prog.execFrom p prog ⟨0, 0, fun _ _ => 0⟩

def CleanlyComputes2 (p : Nat) (prog : List Pass2Instr) (f : List Nat) : Prop :=
  let st := Pass2Prog.exec p prog
  st.b % p = 0 ∧ st.a % p = 0 ∧
  ∀ dR dx : Nat, st.coeff dR dx % p = (if dR = 0 then f.getD dx 0 else 0) % p

def InRPPass2 (p t : Nat) (f : List Nat) : Prop :=
  ∃ prog : List Pass2Instr, Pass2Prog.accesses prog ≤ t ∧ CleanlyComputes2 p prog f

def monomial (d : Nat) : List Nat :=
  List.replicate d 0 ++ [1]

def sumR {R : Type u} [CRing R] : Nat → (Nat → R) → R
  | 0, _     => 0
  | n + 1, f => sumR n f + f n

def evalPolyR {R : Type u} [CRing R] (poly : List Nat) (t : R) : R :=
  sumR poly.length (fun k => CRing.natCast (poly.getD k 0) * CRing.pow t k)

def Pass2Instr.execRing {R : Type u} [CRing R] (x : R) : R × R → Pass2Instr → R × R
  | (o, r), .addOut poly      => (o + evalPolyR poly r, r)
  | (o, r), .addWorkConst c   => (o, r + CRing.natCast c)
  | (o, r), .addInputOut lam  => (o + CRing.natCast lam * x, r)
  | (o, r), .addInputWork lam => (o, r + CRing.natCast lam * x)

def Pass2Prog.execRing {R : Type u} [CRing R] (x : R) : List Pass2Instr → R × R → R × R
  | [], st        => st
  | i :: rest, st => Pass2Prog.execRing x rest (i.execRing x st)

/-! ## 4. Strictly Bilinear Passive Programs (`T2`) -/

inductive BilinInstr (n : Nat) where
  | mulAdd (dst a b : Fin n) : BilinInstr n
  | addInput (dst : Fin n) : BilinInstr n

def BilinProg.accesses {n : Nat} : List (BilinInstr n) → Nat
  | [] => 0
  | .mulAdd _ _ _ :: rest => BilinProg.accesses rest
  | .addInput _ :: rest => 1 + BilinProg.accesses rest

def BilinProg.bilinOps {n : Nat} : List (BilinInstr n) → Nat
  | [] => 0
  | .mulAdd _ _ _ :: rest => 1 + BilinProg.bilinOps rest
  | .addInput _ :: rest => BilinProg.bilinOps rest

def BilinInstr.isValidPassive {n : Nat} : BilinInstr n → Prop
  | .mulAdd dst a b => dst ≠ a ∧ dst ≠ b ∧ a.val ≠ 0 ∧ b.val ≠ 0
  | .addInput _ => True

def BilinInstr.exec {n : Nat} {R : Type u} [CRing R]
    (x : R) (st : Fin n → R) : BilinInstr n → (Fin n → R)
  | .mulAdd dst a b => fun i => if i = dst then st dst + st a * st b else st i
  | .addInput dst => fun i => if i = dst then st dst + x else st i

def BilinProg.exec {n : Nat} {R : Type u} [CRing R]
    (x : R) : List (BilinInstr n) → (Fin n → R) → (Fin n → R)
  | [], st => st
  | instr :: rest, st => BilinProg.exec x rest (instr.exec x st)

/-! ## 5. Three- & Four-Register Passive Powering and Streaming (`T3a`–`T3i`) -/

inductive Pass3InstrR (R : Type u) where
  | addOut (terms : List (Nat × Nat × R)) : Pass3InstrR R
  | addWorkV (coeff : R) (deg : Nat) : Pass3InstrR R
  | addInputU (alpha : R) : Pass3InstrR R

def Pass3Prog.accesses {R : Type u} : List (Pass3InstrR R) → Nat
  | [] => 0
  | .addOut _ :: rest => Pass3Prog.accesses rest
  | .addWorkV _ _ :: rest => Pass3Prog.accesses rest
  | .addInputU _ :: rest => 1 + Pass3Prog.accesses rest

def evalBivar {R : Type u} [CRing R] (u v : R) : List (Nat × Nat × R) → R
  | [] => 0
  | (a, b, c) :: rest => c * (CRing.pow u a * CRing.pow v b) + evalBivar u v rest

def Pass3InstrR.exec {R : Type u} [CRing R] (x : R) (st : R × R × R) :
    Pass3InstrR R → R × R × R
  | .addOut terms => (st.1 + evalBivar st.2.1 st.2.2 terms, st.2.1, st.2.2)
  | .addWorkV c d => (st.1, st.2.1, st.2.2 + c * CRing.pow st.2.1 d)
  | .addInputU α => (st.1, st.2.1 + α * x, st.2.2)

def Pass3Prog.exec {R : Type u} [CRing R] (x : R) :
    List (Pass3InstrR R) → (R × R × R) → (R × R × R)
  | [], st => st
  | i :: rest, st => Pass3Prog.exec x rest (i.exec x st)

inductive Work3Instr (R : Type u) where
  | addX (dst : Fin 3) (c : R) : Work3Instr R
  | addPoly (dst : Fin 3) (terms : List (Nat × Nat × R)) : Work3Instr R

def Work3Prog.accesses {R : Type u} : List (Work3Instr R) → Nat
  | [] => 0
  | .addX _ _ :: rest => 1 + Work3Prog.accesses rest
  | .addPoly _ _ :: rest => Work3Prog.accesses rest

def Work3Instr.exec {R : Type u} [CRing R] (x : R) (st : R × R × R) :
    Work3Instr R → R × R × R
  | .addX dst c =>
    match dst.val with
    | 0 => (st.1 + c * x, st.2.1, st.2.2)
    | 1 => (st.1, st.2.1 + c * x, st.2.2)
    | _ => (st.1, st.2.1, st.2.2 + c * x)
  | .addPoly dst terms =>
    match dst.val with
    | 0 => (st.1 + evalBivar st.2.1 st.2.2 terms, st.2.1, st.2.2)
    | 1 => (st.1, st.2.1 + evalBivar st.2.2 st.1 terms, st.2.2)
    | _ => (st.1, st.2.1, st.2.2 + evalBivar st.1 st.2.1 terms)

inductive Pass4Instr (R : Type u) where
  | work (w : Work3Instr R) : Pass4Instr R
  | outAddPow (coeff : R) (deg : Nat) : Pass4Instr R

def Pass4Prog.accesses {R : Type u} : List (Pass4Instr R) → Nat
  | [] => 0
  | .work w :: rest => Work3Prog.accesses [w] + Pass4Prog.accesses rest
  | .outAddPow _ _ :: rest => Pass4Prog.accesses rest

def Pass4Instr.exec {R : Type u} [CRing R] (x : R) (st : R × R × R × R) :
    Pass4Instr R → R × R × R × R
  | .work w =>
    let w' := w.exec x st.2
    (st.1, w'.1, w'.2.1, w'.2.2)
  | .outAddPow coeff d =>
    (st.1 + coeff * CRing.pow st.2.1 d, st.2.1, st.2.2.1, st.2.2.2)

def Pass4Prog.exec {R : Type u} [CRing R] (x : R) :
    List (Pass4Instr R) → (R × R × R × R) → (R × R × R × R)
  | [], st => st
  | i :: rest, st => Pass4Prog.exec x rest (i.exec x st)

instance instCRingFinFun {n : Nat} {R : Type u} [CRing R] : CRing (Fin n → R) where
  zero := fun _ => 0
  one := fun _ => 1
  add f g := fun i => f i + g i
  mul f g := fun i => f i * g i
  neg f := fun i => -(f i)
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

/-! ## 6. Balanced Zero-Workspace Bilinear Product (`T4`) -/

inductive CatOp where
  | addInput (dst : Nat) (sign : Int) (varIdx : Nat) : CatOp
  | addProd (dst a b : Nat) (sign : Int) : CatOp

def CatOp.isStrictValid : CatOp → Prop
  | .addInput _ s _ => s = 1 ∨ s = -1
  | .addProd dst a b s => (s = 1 ∨ s = -1) ∧ dst ≠ a ∧ dst ≠ b ∧ a ≠ b

def CatOp.exec {R : Type u} [CRing R] (xs : Nat → R) (st : Nat → R) : CatOp → (Nat → R)
  | .addInput dst s v =>
    fun r => if r = dst then st dst + CRing.intCast s * xs v else st r
  | .addProd dst a b s =>
    fun r => if r = dst then st dst + CRing.intCast s * (st a * st b) else st r

def CatProg.exec {R : Type u} [CRing R] (xs : Nat → R) : List CatOp → (Nat → R) → (Nat → R)
  | [], st => st
  | op :: rest, st => CatProg.exec xs rest (op.exec xs st)

def rangeProd {R : Type u} [CRing R] (xs : Nat → R) (offset : Nat) : Nat → R
  | 0 => 1
  | n + 1 => rangeProd xs offset n * xs (offset + n)

end

/-! ## Private Equivalence Bridges to `Catalytic.*` -/

universe u

@[instance_reducible]
private def toCatCRing {R : Type u} (inst : CRing R) : Catalytic.CRing R where
  add := inst.add
  mul := inst.mul
  neg := inst.neg
  zero := inst.zero
  one := inst.one
  add_assoc := inst.add_assoc
  add_comm := inst.add_comm
  zero_add := inst.zero_add
  add_neg := inst.add_neg
  mul_assoc := inst.mul_assoc
  mul_comm := inst.mul_comm
  one_mul := inst.one_mul
  left_distrib := inst.left_distrib

@[instance_reducible]
private def toCatChar2CRing {R : Type u} (inst : Char2CRing R) : Catalytic.Char2CRing R where
  toCRing := toCatCRing inst.toCRing
  add_self := inst.add_self

private theorem natCast_eq {R : Type u} (inst : CRing R) :
    ∀ n : Nat, @CRing.natCast R inst n = @Catalytic.CRing.natCast R (toCatCRing inst) n
  | 0 => rfl
  | n + 1 => congrArg (fun z => @Add.add R inst.toAdd z (@One.one R inst.toOne)) (natCast_eq inst n)

private theorem intCast_eq {R : Type u} (inst : CRing R) :
    ∀ z : Int, @CRing.intCast R inst z = @Catalytic.CRing.intCast R (toCatCRing inst) z
  | Int.ofNat n => natCast_eq inst n
  | Int.negSucc n => congrArg (@Neg.neg R inst.toNeg) (natCast_eq inst (n + 1))

private theorem pow_eq {R : Type u} (inst : CRing R) (a : R) :
    ∀ n : Nat, @CRing.pow R inst a n = @Catalytic.CRing.pow R (toCatCRing inst) a n
  | 0 => rfl
  | n + 1 => congrArg (fun z => @Mul.mul R inst.toMul z a) (pow_eq inst a n)

private theorem fact_eq : ∀ n, fact n = Catalytic.fact n
  | 0 => rfl
  | n + 1 => congrArg ((n + 1) * ·) (fact_eq n)

private theorem choose_eq : ∀ n k, choose n k = Catalytic.choose n k
  | n, 0 => by cases n <;> rfl
  | 0, _ + 1 => rfl
  | n + 1, k + 1 => by
    simp only [choose, Catalytic.choose, choose_eq n k, choose_eq n (k + 1)]

private theorem sumNat_eq (n : Nat) (f : Nat → Nat) : sumNat n f = Catalytic.sumNat n f := by
  induction n with
  | zero => rfl
  | succ m ih => simp only [sumNat, Catalytic.sumNat, ih]

private theorem digitSumFuel_eq (p : Nat) :
    ∀ fuel n : Nat, n < fuel → digitSumFuel p fuel n = Catalytic.digitSum p n
  | 0, _, h => by omega
  | fuel + 1, n, h => by
    unfold digitSumFuel
    by_cases hp : 2 ≤ p
    · by_cases hn : n = 0
      · subst hn
        simp [Catalytic.digitSum_zero]
      · simp only [hp, ↓reduceIte, hn]
        rw [Catalytic.digitSum_eq hp n hn]
        have hlt : n / p < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by omega)
        rw [digitSumFuel_eq p fuel (n / p) (by omega)]
    · simp only [hp, ↓reduceIte]
      unfold Catalytic.digitSum
      simp [hp]

private theorem digitSum_eq (p n : Nat) : digitSum p n = Catalytic.digitSum p n :=
  digitSumFuel_eq p (n + 1) n (Nat.lt_succ_self n)

private theorem baseDigitsFuel_eq (δ : Nat) (hδ : 2 ≤ δ) :
    ∀ fuel N : Nat, N < fuel → baseDigitsFuel δ fuel N = Catalytic.baseDigits δ hδ N
  | 0, _, h => by omega
  | fuel + 1, N, h => by
    unfold baseDigitsFuel Catalytic.baseDigits
    by_cases hlt : N < δ
    · simp [hlt]
    · simp only [hlt, ↓reduceIte, ↓reduceDIte]
      have hdiv : N / δ < N := Nat.div_lt_self (by omega) (by omega)
      rw [baseDigitsFuel_eq δ hδ fuel (N / δ) (by omega)]

private theorem baseDigits_eq (δ : Nat) (hδ : 2 ≤ δ) (N : Nat) :
    baseDigits δ N = Catalytic.baseDigits δ hδ N :=
  baseDigitsFuel_eq δ hδ (N + 1) N (Nat.lt_succ_self N)

private def p2ToCat : Pass2Instr → Catalytic.Pass2Instr
  | .addOut poly => .addOut poly
  | .addWorkConst c => .addWorkConst c
  | .addInputOut lam => .addInputOut lam
  | .addInputWork lam => .addInputWork lam

private def p2FromCat : Catalytic.Pass2Instr → Pass2Instr
  | .addOut poly => .addOut poly
  | .addWorkConst c => .addWorkConst c
  | .addInputOut lam => .addInputOut lam
  | .addInputWork lam => .addInputWork lam

private theorem p2_accesses_to (prog : List Pass2Instr) :
    Catalytic.Pass2Prog.accesses (prog.map p2ToCat) = Pass2Prog.accesses prog := by
  induction prog with
  | nil => rfl
  | cons i rest ih => cases i <;> simp [p2ToCat, Pass2Prog.accesses, Catalytic.Pass2Prog.accesses, ih]

private theorem p2_accesses_from (prog : List Catalytic.Pass2Instr) :
    Pass2Prog.accesses (prog.map p2FromCat) = Catalytic.Pass2Prog.accesses prog := by
  induction prog with
  | nil => rfl
  | cons i rest ih => cases i <;> simp [p2FromCat, Pass2Prog.accesses, Catalytic.Pass2Prog.accesses, ih]

private theorem polyAtShiftCoeff_eq (poly : List Nat) (b a dR dx : Nat) :
    polyAtShiftCoeff poly b a dR dx = Catalytic.polyAtShiftCoeff poly b a dR dx := by
  unfold polyAtShiftCoeff Catalytic.polyAtShiftCoeff
  dsimp only
  have h1 : sumNat poly.length (fun k => poly.getD k 0 * choose k (dR + dx) * b ^ (k - (dR + dx))) =
      Catalytic.sumNat poly.length (fun k => poly.getD k 0 * Catalytic.choose k (dR + dx) * b ^ (k - (dR + dx))) := by
    rw [sumNat_eq]
    congr 1; funext k; rw [choose_eq]
  rw [h1, choose_eq]

private theorem p2_execFrom_to (p : Nat) (prog : List Pass2Instr)
    (st : State2) (cst : Catalytic.State2)
    (hb : st.b = cst.b) (ha : st.a = cst.a) (hc : st.coeff = cst.coeff) :
    let r1 := Pass2Prog.execFrom p prog st
    let r2 := Catalytic.Pass2Prog.execFrom p (prog.map p2ToCat) cst
    r1.b = r2.b ∧ r1.a = r2.a ∧ r1.coeff = r2.coeff := by
  induction prog generalizing st cst with
  | nil => exact ⟨hb, ha, hc⟩
  | cons i rest ih =>
    cases i with
    | addOut poly =>
      apply ih
      · exact hb
      · exact ha
      · funext dR dx
        simp [Pass2Instr.exec, Catalytic.Pass2Instr.exec, p2ToCat, hb, ha, hc, polyAtShiftCoeff_eq]
    | addWorkConst c =>
      apply ih
      · simp [Pass2Instr.exec, Catalytic.Pass2Instr.exec, p2ToCat, hb]
      · exact ha
      · exact hc
    | addInputOut lam =>
      apply ih
      · exact hb
      · exact ha
      · funext dR dx; simp [Pass2Instr.exec, Catalytic.Pass2Instr.exec, p2ToCat, hc]
    | addInputWork lam =>
      apply ih
      · exact hb
      · simp [Pass2Instr.exec, Catalytic.Pass2Instr.exec, p2ToCat, ha]
      · exact hc

private theorem p2_to_from (prog : List Catalytic.Pass2Instr) :
    (prog.map p2FromCat).map p2ToCat = prog := by
  induction prog with
  | nil => rfl
  | cons i rest ih => cases i <;> simp [p2FromCat, p2ToCat, ih]

private theorem clean2_iff_to (p : Nat) (prog : List Pass2Instr) (f : List Nat) :
    CleanlyComputes2 p prog f ↔ Catalytic.CleanlyComputes2 p (prog.map p2ToCat) f := by
  have h := p2_execFrom_to p prog ⟨0, 0, fun _ _ => 0⟩ ⟨0, 0, fun _ _ => 0⟩ rfl rfl rfl
  rcases h with ⟨hb, ha, hc⟩
  unfold CleanlyComputes2 Catalytic.CleanlyComputes2 Pass2Prog.exec Catalytic.Pass2Prog.exec
  dsimp only
  rw [hb, ha, hc]

private theorem inRPPass2_iff (p t : Nat) (f : List Nat) :
    InRPPass2 p t f ↔ Catalytic.InRPPass2 p t f := by
  constructor
  · rintro ⟨prog, hacc, hcl⟩
    refine ⟨prog.map p2ToCat, ?_, (clean2_iff_to p prog f).mp hcl⟩
    rw [p2_accesses_to]; exact hacc
  · rintro ⟨prog, hacc, hcl⟩
    refine ⟨prog.map p2FromCat, ?_, ?_⟩
    · rw [p2_accesses_from]; exact hacc
    · rw [clean2_iff_to, p2_to_from]; exact hcl

private theorem sumR_eq {R : Type u} (inst : CRing R) (n : Nat) (f : Nat → R) :
    @sumR R inst n f = @Catalytic.sumR R (toCatCRing inst) n f := by
  induction n with
  | zero => rfl
  | succ m ih => exact congrArg (fun z => @Add.add R inst.toAdd z (f m)) ih

private theorem evalPolyR_eq {R : Type u} (inst : CRing R) (poly : List Nat) (t : R) :
    @evalPolyR R inst poly t = @Catalytic.evalPolyR R (toCatCRing inst) poly t := by
  unfold evalPolyR Catalytic.evalPolyR
  rw [sumR_eq inst]
  congr 1; funext k
  rw [natCast_eq inst, pow_eq inst]

private theorem p2_execRing_eq {R : Type u} (inst : CRing R) (x : R)
    (prog : List Pass2Instr) (st : R × R) :
    @Pass2Prog.execRing R inst x prog st =
      @Catalytic.Pass2Prog.execRing R (toCatCRing inst) x (prog.map p2ToCat) st := by
  induction prog generalizing st with
  | nil => rfl
  | cons i rest ih =>
    rcases st with ⟨o, r⟩
    cases i with
    | addOut poly =>
      simp only [List.map, p2ToCat, Pass2Prog.execRing, Catalytic.Pass2Prog.execRing,
        Pass2Instr.execRing, Catalytic.Pass2Instr.execRing]
      rw [evalPolyR_eq inst]
      exact ih _
    | addWorkConst c =>
      simp only [List.map, p2ToCat, Pass2Prog.execRing, Catalytic.Pass2Prog.execRing,
        Pass2Instr.execRing, Catalytic.Pass2Instr.execRing]
      rw [natCast_eq inst]
      exact ih _
    | addInputOut lam =>
      simp only [List.map, p2ToCat, Pass2Prog.execRing, Catalytic.Pass2Prog.execRing,
        Pass2Instr.execRing, Catalytic.Pass2Instr.execRing]
      rw [natCast_eq inst]
      exact ih _
    | addInputWork lam =>
      simp only [List.map, p2ToCat, Pass2Prog.execRing, Catalytic.Pass2Prog.execRing,
        Pass2Instr.execRing, Catalytic.Pass2Instr.execRing]
      rw [natCast_eq inst]
      exact ih _

private def bilinFromCat {n : Nat} : Catalytic.BilinInstr n → BilinInstr n
  | .mulAdd d a b => .mulAdd d a b
  | .addInput d => .addInput d

private theorem bilin_accesses {n : Nat} (p : List (Catalytic.BilinInstr n)) :
    BilinProg.accesses (p.map bilinFromCat) = Catalytic.BilinProg.accesses p := by
  induction p with
  | nil => rfl
  | cons i rest ih => cases i <;> simp [bilinFromCat, BilinProg.accesses, Catalytic.BilinProg.accesses, ih]

private theorem bilin_ops {n : Nat} (p : List (Catalytic.BilinInstr n)) :
    BilinProg.bilinOps (p.map bilinFromCat) = Catalytic.BilinProg.bilinOps p := by
  induction p with
  | nil => rfl
  | cons i rest ih => cases i <;> simp [bilinFromCat, BilinProg.bilinOps, Catalytic.BilinProg.bilinOps, ih]

private theorem bilin_exec {n : Nat} {R : Type u} (inst : CRing R) (x : R)
    (p : List (Catalytic.BilinInstr n)) (st : Fin n → R) :
    @BilinProg.exec n R inst x (p.map bilinFromCat) st =
      @Catalytic.BilinProg.exec n R (toCatCRing inst) x p st := by
  induction p generalizing st with
  | nil => rfl
  | cons i rest ih =>
    cases i <;> exact ih _

private def pass3FromCat {R : Type u} : Catalytic.Pass3InstrR R → Pass3InstrR R
  | .addOut terms => .addOut terms
  | .addWorkV c d => .addWorkV c d
  | .addInputU a => .addInputU a

private theorem pass3_accesses {R : Type u} (p : List (Catalytic.Pass3InstrR R)) :
    Pass3Prog.accesses (p.map pass3FromCat) = Catalytic.Pass3Prog.accesses p := by
  induction p with
  | nil => rfl
  | cons i rest ih => cases i <;> simp [pass3FromCat, Pass3Prog.accesses, Catalytic.Pass3Prog.accesses, ih]

private theorem evalBivar_eq {R : Type u} (inst : CRing R) (u v : R) :
    ∀ terms : List (Nat × Nat × R),
      @evalBivar R inst u v terms = @Catalytic.evalBivar R (toCatCRing inst) u v terms
  | [] => rfl
  | (a, b, c) :: rest => by
    simp only [evalBivar, Catalytic.evalBivar]
    rw [pow_eq inst u a, pow_eq inst v b, evalBivar_eq inst u v rest]

private theorem pass3_exec {R : Type u} (inst : CRing R) (x : R)
    (p : List (Catalytic.Pass3InstrR R)) (st : R × R × R) :
    @Pass3Prog.exec R inst x (p.map pass3FromCat) st =
      @Catalytic.Pass3Prog.exec R (toCatCRing inst) x p st := by
  induction p generalizing st with
  | nil => rfl
  | cons i rest ih =>
    cases i with
    | addOut terms =>
      simp only [List.map, pass3FromCat, Pass3Prog.exec, Catalytic.Pass3Prog.exec,
        Pass3InstrR.exec, Catalytic.Pass3InstrR.exec]
      rw [evalBivar_eq inst]
      exact ih _
    | addWorkV c d =>
      simp only [List.map, pass3FromCat, Pass3Prog.exec, Catalytic.Pass3Prog.exec,
        Pass3InstrR.exec, Catalytic.Pass3InstrR.exec]
      rw [pow_eq inst]
      exact ih _
    | addInputU a =>
      exact ih _

private def work3FromCat {R : Type u} : Catalytic.Work3Instr R → Work3Instr R
  | .addX d c => .addX d c
  | .addPoly d t => .addPoly d t

private def pass4FromCat {R : Type u} : Catalytic.Pass4Instr R → Pass4Instr R
  | .work w => .work (work3FromCat w)
  | .outAddPow c d => .outAddPow c d

private theorem pass4_accesses {R : Type u} (p : List (Catalytic.Pass4Instr R)) :
    Pass4Prog.accesses (p.map pass4FromCat) = Catalytic.Pass4Prog.accesses p := by
  induction p with
  | nil => rfl
  | cons i rest ih =>
    cases i with
    | work w => cases w <;> simp [pass4FromCat, work3FromCat, Pass4Prog.accesses,
        Catalytic.Pass4Prog.accesses, Work3Prog.accesses, Catalytic.Work3Prog.accesses, ih]
    | outAddPow _ _ => simp [pass4FromCat, Pass4Prog.accesses, Catalytic.Pass4Prog.accesses, ih]

private theorem work3_exec {R : Type u} (inst : CRing R) (x : R) (st : R × R × R)
    (w : Catalytic.Work3Instr R) :
    @Work3Instr.exec R inst x st (work3FromCat w) =
      @Catalytic.Work3Instr.exec R (toCatCRing inst) x st w := by
  cases w with
  | addX d c => rfl
  | addPoly d terms =>
    simp only [work3FromCat, Work3Instr.exec, Catalytic.Work3Instr.exec, evalBivar_eq inst]
    rfl

private theorem pass4_exec {R : Type u} (inst : CRing R) (x : R)
    (p : List (Catalytic.Pass4Instr R)) (st : R × R × R × R) :
    @Pass4Prog.exec R inst x (p.map pass4FromCat) st =
      @Catalytic.Pass4Prog.exec R (toCatCRing inst) x p st := by
  induction p generalizing st with
  | nil => rfl
  | cons i rest ih =>
    cases i with
    | work w =>
      simp only [List.map, pass4FromCat, Pass4Prog.exec, Catalytic.Pass4Prog.exec,
        Pass4Instr.exec, Catalytic.Pass4Instr.exec]
      rw [work3_exec inst]
      exact ih _
    | outAddPow c d =>
      simp only [List.map, pass4FromCat, Pass4Prog.exec, Catalytic.Pass4Prog.exec,
        Pass4Instr.exec, Catalytic.Pass4Instr.exec]
      rw [pow_eq inst]
      exact ih _

private def catOpFromCat : Catalytic.CatOp → CatOp
  | .addInput d s v => .addInput d s v
  | .addProd d a b s => .addProd d a b s

private theorem catProg_exec {R : Type u} (inst : CRing R) (xs : Nat → R)
    (p : List Catalytic.CatOp) (st : Nat → R) :
    @CatProg.exec R inst xs (p.map catOpFromCat) st =
      @Catalytic.CatProg.exec R (toCatCRing inst) xs p st := by
  induction p generalizing st with
  | nil => rfl
  | cons op rest ih =>
    cases op with
    | addInput d s v =>
      simp only [List.map, catOpFromCat, CatProg.exec, Catalytic.CatProg.exec,
        CatOp.exec, Catalytic.CatOp.exec]
      rw [intCast_eq inst]
      exact ih _
    | addProd d a b s =>
      simp only [List.map, catOpFromCat, CatProg.exec, Catalytic.CatProg.exec,
        CatOp.exec, Catalytic.CatOp.exec]
      rw [intCast_eq inst]
      exact ih _

private theorem rangeProd_eq {R : Type u} (inst : CRing R) (xs : Nat → R) (offset : Nat) :
    ∀ n : Nat, @rangeProd R inst xs offset n = @Catalytic.rangeProd R (toCatCRing inst) xs offset n
  | 0 => rfl
  | n + 1 => congrArg (fun z => @Mul.mul R inst.toMul z (xs (offset + n))) (rangeProd_eq inst xs offset n)

/-! ## 7. Verified Proofs of All 17 Headline Challenge Theorems -/

public theorem t1_digit_sum_dichotomy :
    ∀ (p t : Nat), IsPrime p → 1 ≤ t → ∀ (f : List Nat),
      InRPPass2 p t f ↔
        ∀ d : Nat, 2 ≤ d → f.getD d 0 % p ≠ 0 →
          digitSum p d ≤ min (p - 1) (t - 1) := by
  intro p t hp ht f
  rw [inRPPass2_iff]
  have h := Catalytic.Solution.t1_digit_sum_dichotomy p t hp ht f
  simpa [digitSum_eq] using h

public theorem t1a_two_access_frobenius_collapse :
    ∀ (p m : Nat), IsPrime p → InRPPass2 p 2 (monomial (p ^ m)) := by
  intro p m hp
  rw [inRPPass2_iff]
  exact Catalytic.Solution.t1a_two_access_frobenius_collapse p m hp

public theorem t1b_f2_saturation :
    ∀ (t : Nat), ¬ InRPPass2 2 t (monomial 3) := by
  intro t
  rw [inRPPass2_iff]
  exact Catalytic.Solution.t1b_f2_saturation t

public theorem t1c_impossibility_threshold :
    ∀ (p d t : Nat), IsPrime p → 2 ≤ d → 1 ≤ t → p ≤ digitSum p d →
      ¬ InRPPass2 p t (monomial d) := by
  intro p d t hp hd ht hs
  rw [inRPPass2_iff]
  rw [digitSum_eq] at hs
  exact Catalytic.Solution.t1c_impossibility_threshold p d t hp hd ht hs

public theorem t1d_vinciguerra_recovery :
    ∀ (p d t : Nat), IsPrime p → 2 ≤ d → d < p → 1 ≤ t →
      (InRPPass2 p t (monomial d) ↔ d + 1 ≤ t) := by
  intro p d t hp hd hdp ht
  rw [inRPPass2_iff]
  exact Catalytic.Solution.t1d_vinciguerra_recovery p d t hp hd hdp ht

public theorem t1s_pass2_ring_soundness :
    ∀ (p : Nat) (prog : List Pass2Instr) (f : List Nat), CleanlyComputes2 p prog f →
      ∀ (R : Type) [CRing R], (CRing.natCast p : R) = 0 →
        ∀ o u x : R, Pass2Prog.execRing x prog (o, u) = (o + evalPolyR f x, u) := by
  intro p prog f hcl R inst hchar o u x
  have hcl' := (clean2_iff_to p prog f).mp hcl
  have hchar' : @Catalytic.CRing.natCast R (toCatCRing inst) p = 0 := by
    rw [← natCast_eq inst]; exact hchar
  have hres := @Catalytic.Solution.t1s_pass2_ring_soundness |>.2 p (prog.map p2ToCat) f hcl' R (toCatCRing inst) hchar' o u x
  rw [p2_execRing_eq inst, evalPolyR_eq inst]
  exact hres

public theorem t2_bilinear_frobenius_collapse :
    ∀ (k : Nat), 1 ≤ k →
      ∃ prog : List (BilinInstr (k + 1)),
        BilinProg.accesses prog = 2 ∧
        BilinProg.bilinOps prog = 4 * k - 2 ∧
        (∀ instr ∈ prog, instr.isValidPassive) ∧
        ∀ (R : Type) [Char2CRing R] (x : R) (init : Fin (k + 1) → R),
          let final := BilinProg.exec x prog init
          final ⟨0, by omega⟩ = init ⟨0, by omega⟩ + CRing.pow x (2 ^ k) ∧
          ∀ i : Fin (k + 1), i.val ≠ 0 → final i = init i := by
  intro k hk
  rcases Catalytic.Solution.t2_bilinear_frobenius_collapse k hk with ⟨hacc, hops, hval, hclean⟩
  refine ⟨(Catalytic.frobBilinProg k hk).map bilinFromCat, ?_, ?_, ?_, ?_⟩
  · rw [bilin_accesses]; exact hacc
  · rw [bilin_ops]; exact hops
  · intro instr hmem
    rcases List.mem_map.mp hmem with ⟨ci, hci, rfl⟩
    have hv := hval ci hci
    cases ci <;> exact hv
  · intro R inst x init
    have hc := @hclean R (toCatChar2CRing inst) x init
    dsimp only at hc ⊢
    rw [bilin_exec inst.toCRing, pow_eq inst.toCRing]
    exact hc

public theorem t3a_three_reg_5call_x7 :
    ∀ (R : Type) [CRing R] (inv576 : R), inv576 * CRing.intCast 576 = 1 →
      ∃ prog : List (Pass3InstrR R),
        Pass3Prog.accesses prog = 5 ∧
        ∀ x o u v : R, Pass3Prog.exec x prog (o, u, v) = (o + CRing.pow x 7, u, v) := by
  intro R inst inv576 hinv
  have hinv' : inv576 * @Catalytic.CRing.intCast R (toCatCRing inst) 576 = 1 := by
    rw [← intCast_eq inst]; exact hinv
  rcases @Catalytic.Solution.t3a_three_reg_5call_x7 R (toCatCRing inst) inv576 hinv' with ⟨hacc, hex⟩
  refine ⟨(@Catalytic.Pass3Prog.scaleOut R (toCatCRing inst) inv576 Catalytic.prog5_x7).map pass3FromCat, ?_, ?_⟩
  · rw [pass3_accesses]; exact hacc
  · intro x o u v
    rw [pass3_exec inst, pow_eq inst]
    exact hex x o u v

public theorem t3b_three_reg_6call_x9 :
    ∀ (R : Type) [CRing R] (invD : R), invD * CRing.intCast 382500000 = 1 →
      ∃ prog : List (Pass3InstrR R),
        Pass3Prog.accesses prog = 6 ∧
        ∀ x o u v : R, Pass3Prog.exec x prog (o, u, v) = (o + CRing.pow x 9, u, v) := by
  intro R inst invD hinv
  have hinv' : invD * @Catalytic.CRing.intCast R (toCatCRing inst) 382500000 = 1 := by
    rw [← intCast_eq inst]; exact hinv
  rcases @Catalytic.Solution.t3b_three_reg_6call_x9 R (toCatCRing inst) invD hinv' with ⟨hacc, hex⟩
  refine ⟨(@Catalytic.Pass3Prog.scaleOut R (toCatCRing inst) invD Catalytic.prog6_x9).map pass3FromCat, ?_, ?_⟩
  · rw [pass3_accesses]; exact hacc
  · intro x o u v
    rw [pass3_exec inst, pow_eq inst]
    exact hex x o u v

public theorem t3c_three_reg_7call_x11 :
    ∀ (R : Type) [CRing R] (invD : R), invD * CRing.intCast 68724637549388656012800 = 1 →
      ∃ prog : List (Pass3InstrR R),
        Pass3Prog.accesses prog = 7 ∧
        ∀ x o u v : R, Pass3Prog.exec x prog (o, u, v) = (o + CRing.pow x 11, u, v) := by
  intro R inst invD hinv
  have hinv' : invD * @Catalytic.CRing.intCast R (toCatCRing inst) 68724637549388656012800 = 1 := by
    rw [← intCast_eq inst]; exact hinv
  rcases @Catalytic.Solution.t3c_three_reg_7call_x11 R (toCatCRing inst) invD hinv' with ⟨hacc, hex⟩
  refine ⟨(@Catalytic.Pass3Prog.scaleOut R (toCatCRing inst) invD Catalytic.prog7_x11).map pass3FromCat, ?_, ?_⟩
  · rw [pass3_accesses]; exact hacc
  · intro x o u v
    rw [pass3_exec inst, pow_eq inst]
    exact hex x o u v

public theorem t3d_three_reg_8call_x13 :
    ∀ (R : Type) [CRing R] (invD : R), invD * CRing.intCast 2656207148788801777680 = 1 →
      ∃ prog : List (Pass3InstrR R),
        Pass3Prog.accesses prog = 8 ∧
        ∀ x o u v : R, Pass3Prog.exec x prog (o, u, v) = (o + CRing.pow x 13, u, v) := by
  intro R inst invD hinv
  have hinv' : invD * @Catalytic.CRing.intCast R (toCatCRing inst) 2656207148788801777680 = 1 := by
    rw [← intCast_eq inst]; exact hinv
  rcases @Catalytic.Solution.t3d_three_reg_8call_x13 R (toCatCRing inst) invD hinv' with ⟨hacc, hex⟩
  refine ⟨(@Catalytic.Pass3Prog.scaleOut R (toCatCRing inst) invD Catalytic.prog8_x13).map pass3FromCat, ?_, ?_⟩
  · rw [pass3_accesses]; exact hacc
  · intro x o u v
    rw [pass3_exec inst, pow_eq inst]
    exact hex x o u v

public theorem t3e_exponent_chain :
    (8 ^ 37 < 13 ^ 30) ∧ (11 ^ 30 < 7 ^ 37) ∧
    (7 ^ 16 < 11 ^ 13) ∧ (9 ^ 13 < 6 ^ 16) ∧
    (6 ^ 11 < 9 ^ 9)   ∧ (7 ^ 9 < 5 ^ 11) ∧
    (5 ^ 6 < 7 ^ 5)    ∧ (5 ^ 5 < 4 ^ 6) ∧
    (15 ^ 30 < 9 ^ 37) :=
  Catalytic.Solution.t3e_exponent_chain

public theorem t3f_global_integer_optimality :
    (8 ^ 37 < 13 ^ 30) ∧
    (∀ t : Nat, 4 ≤ t → t ≠ 8 → (2 * t - 3) ^ 30 < t ^ 37) :=
  Catalytic.Solution.t3f_global_integer_optimality

public theorem t3g_three_reg_9call_x15 :
    ∀ (R : Type) [CRing R] (invD : R),
      invD * CRing.intCast 876702103804656272895371895753963647960420947968000 = 1 →
      ∃ prog : List (Pass3InstrR R),
        Pass3Prog.accesses prog = 9 ∧
        ∀ x o u v : R, Pass3Prog.exec x prog (o, u, v) = (o + CRing.pow x 15, u, v) := by
  intro R inst invD hinv
  have hinv' : invD * @Catalytic.CRing.intCast R (toCatCRing inst) 876702103804656272895371895753963647960420947968000 = 1 := by
    rw [← intCast_eq inst]; exact hinv
  rcases @Catalytic.Solution.t3g_three_reg_9call_x15 R (toCatCRing inst) invD hinv' with ⟨hacc, hex⟩
  refine ⟨(@Catalytic.Pass3Prog.scaleOut R (toCatCRing inst) invD Catalytic.prog9_x15).map pass3FromCat, ?_, ?_⟩
  · rw [pass3_accesses]; exact hacc
  · intro x o u v
    rw [pass3_exec inst, pow_eq inst]
    exact hex x o u v

public theorem t3h_four_reg_powering :
    (∀ (R : Type) [CRing R] (N : Nat), 1 ≤ N →
      ∀ (invD8 invFact12 invFactLen : R),
      invD8 * CRing.intCast 2656207148788801777680 = 1 →
      invFact12 * CRing.natCast (fact 12) = 1 →
      invFactLen * CRing.natCast (fact (baseDigits 13 N).length) = 1 →
      ∃ prog : List (Pass4Instr R),
        let ℓ := (baseDigits 13 N).length - 1
        13 ^ ℓ ≤ N ∧
        3 * Pass4Prog.accesses prog < 104 * 8 ^ ℓ ∧
        ∀ x o u r1 r2 : R,
          Pass4Prog.exec x prog (o, u, r1, r2) = (o + CRing.pow x N, u, r1, r2)) ∧
    (∀ (R : Type) [CRing R] (N : Nat), 1 ≤ N →
      ∀ (invFact6 invFactLen : R),
      invFact6 * CRing.natCast (fact 6) = 1 →
      invFactLen * CRing.natCast (fact (baseDigits 7 N).length) = 1 →
      ∃ prog : List (Pass4Instr R),
        let ℓ := (baseDigits 7 N).length - 1
        7 ^ ℓ ≤ N ∧
        3 * Pass4Prog.accesses prog < 70 * 5 ^ ℓ ∧
        ∀ x o u r1 r2 : R,
          Pass4Prog.exec x prog (o, u, r1, r2) = (o + CRing.pow x N, u, r1, r2)) := by
  constructor
  · intro R inst N hN invD8 invF12 invFL hD8 hF12 hFL
    have hD8' : invD8 * @Catalytic.CRing.intCast R (toCatCRing inst) 2656207148788801777680 = 1 := by
      rw [← intCast_eq inst]; exact hD8
    have hF12' : invF12 * @Catalytic.CRing.natCast R (toCatCRing inst) (Catalytic.fact 12) = 1 := by
      rw [← fact_eq, ← natCast_eq inst]; exact hF12
    have hFL' : invFL * @Catalytic.CRing.natCast R (toCatCRing inst) (Catalytic.fact (Catalytic.baseDigits 13 (by decide) N).length) = 1 := by
      rw [← baseDigits_eq 13 (by decide) N, ← fact_eq, ← natCast_eq inst]; exact hFL
    have hmain := Catalytic.Solution.t3h_four_reg_powering.1
    rcases @hmain R (toCatCRing inst) N hN invD8 invF12 invFL hD8' hF12' hFL' with
      ⟨prog, hle, hacc, hex⟩
    refine ⟨prog.map pass4FromCat, ?_, ?_, ?_⟩
    · rw [baseDigits_eq 13 (by decide) N]; exact hle
    · rw [baseDigits_eq 13 (by decide) N, pass4_accesses]; exact hacc
    · intro x o u r1 r2
      rw [pass4_exec inst, pow_eq inst]
      exact hex x o u r1 r2
  · intro R inst N hN invF6 invFL hF6 hFL
    have hF6' : invF6 * @Catalytic.CRing.natCast R (toCatCRing inst) (Catalytic.fact 6) = 1 := by
      rw [← fact_eq, ← natCast_eq inst]; exact hF6
    have hFL' : invFL * @Catalytic.CRing.natCast R (toCatCRing inst) (Catalytic.fact (Catalytic.baseDigits 7 (by decide) N).length) = 1 := by
      rw [← baseDigits_eq 7 (by decide) N, ← fact_eq, ← natCast_eq inst]; exact hFL
    have hmain := Catalytic.Solution.t3h_four_reg_powering.2
    rcases @hmain R (toCatCRing inst) N hN invF6 invFL hF6' hFL' with
      ⟨prog, hle, hacc, hex⟩
    refine ⟨prog.map pass4FromCat, ?_, ?_, ?_⟩
    · rw [baseDigits_eq 7 (by decide) N]; exact hle
    · rw [baseDigits_eq 7 (by decide) N, pass4_accesses]; exact hacc
    · intro x o u r1 r2
      rw [pass4_exec inst, pow_eq inst]
      exact hex x o u r1 r2

public theorem t3i_streaming_frequency_moment :
    ∀ (R : Type) [CRing R] (n D : Nat), 1 ≤ D →
      ∀ (invD8 invFact12 invFactLen : R),
      invD8 * CRing.intCast 2656207148788801777680 = 1 →
      invFact12 * CRing.natCast (fact 12) = 1 →
      invFactLen * CRing.natCast (fact (baseDigits 13 D).length) = 1 →
      ∃ prog : List (Pass4Instr (Fin n → R)),
        let ℓ := (baseDigits 13 D).length - 1
        13 ^ ℓ ≤ D ∧
        3 * Pass4Prog.accesses prog < 104 * 8 ^ ℓ ∧
        ∀ f o u r1 r2 : Fin n → R,
          let res := Pass4Prog.exec f prog (o, u, r1, r2)
          (∀ i : Fin n, res.1 i = o i + CRing.pow (f i) D) ∧
          res.2 = (u, r1, r2) ∧
          sumFin res.1 = sumFin o + sumFin (fun i => CRing.pow (f i) D) := by
  intro R inst n D hD invD8 invF12 invFL hD8 hF12 hFL
  have hD8' : invD8 * @Catalytic.CRing.intCast R (toCatCRing inst) 2656207148788801777680 = 1 := by
    rw [← intCast_eq inst]; exact hD8
  have hF12' : invF12 * @Catalytic.CRing.natCast R (toCatCRing inst) (Catalytic.fact 12) = 1 := by
    rw [← fact_eq, ← natCast_eq inst]; exact hF12
  have hFL' : invFL * @Catalytic.CRing.natCast R (toCatCRing inst) (Catalytic.fact (Catalytic.baseDigits 13 (by decide) D).length) = 1 := by
    rw [← baseDigits_eq 13 (by decide) D, ← fact_eq, ← natCast_eq inst]; exact hFL
  rcases @Catalytic.Solution.t3i_streaming_frequency_moment R (toCatCRing inst) n D hD invD8 invF12 invFL hD8' hF12' hFL' with
    ⟨prog, hle, hacc, hex⟩
  refine ⟨prog.map pass4FromCat, ?_, ?_, ?_⟩
  · rw [baseDigits_eq 13 (by decide) D]; exact hle
  · rw [baseDigits_eq 13 (by decide) D, pass4_accesses]; exact hacc
  · intro f o u r1 r2
    have hfinInst : toCatCRing (@instCRingFinFun n R inst) = @Catalytic.instCRingFinFun n R (toCatCRing inst) := rfl
    have hExec : @Pass4Prog.exec (Fin n → R) (@instCRingFinFun n R inst) f (prog.map pass4FromCat) (o, u, r1, r2) =
        @Catalytic.Pass4Prog.exec (Fin n → R) (@Catalytic.instCRingFinFun n R (toCatCRing inst)) f prog (o, u, r1, r2) := by
      rw [← hfinInst]
      exact pass4_exec (@instCRingFinFun n R inst) f prog (o, u, r1, r2)
    rcases hex f o u r1 r2 with ⟨hpt, hrest, hsum⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i
      rw [hExec, pow_eq inst]
      exact hpt i
    · rw [hExec]; exact hrest
    · rw [hExec]
      unfold sumFin
      rw [sumR_eq inst, sumR_eq inst, sumR_eq inst]
      have hf : (fun j => if h : j < n then @CRing.pow R inst (f ⟨j, h⟩) D else 0) =
          (fun j => if h : j < n then @Catalytic.CRing.pow R (toCatCRing inst) (f ⟨j, h⟩) D else 0) := by
        funext j; by_cases h : j < n <;> simp [h, pow_eq inst]
      rw [hf]
      exact hsum

public theorem t4_balanced_multilinear_product :
    ∀ (k target : Nat) (sign : Int) (pool : List Nat) (offset : Nat),
      (sign = 1 ∨ sign = -1) →
      (k = 0 ∨ k + 1 ≤ pool.length) →
      (target :: pool).Nodup →
      ∃ prog : List CatOp,
        3 * prog.length + 4 = 7 * (2 ^ k) ^ 2 ∧
        (∀ op ∈ prog, op.isStrictValid) ∧
        ∀ (R : Type) [CRing R] (xs st : Nat → R),
          CatProg.exec xs prog st =
            (fun r => if r = target then st target + CRing.intCast sign * rangeProd xs offset (2 ^ k)
                      else st r) := by
  intro k target sign pool offset hsign hpool hnd
  rcases Catalytic.Solution.t4_balanced_multilinear_product k target sign pool offset hsign hpool hnd with
    ⟨hlen, hval, hclean⟩
  refine ⟨(Catalytic.balancedProdProg k target sign pool offset).map catOpFromCat, ?_, ?_, ?_⟩
  · rw [List.length_map]; exact hlen
  · intro op hmem
    rcases List.mem_map.mp hmem with ⟨cop, hcop, rfl⟩
    have hv := hval cop hcop
    cases cop <;> exact hv
  · intro R inst xs st
    rw [catProg_exec inst, intCast_eq inst, rangeProd_eq inst]
    exact @hclean R (toCatCRing inst) xs st

end Catalytic.Palomar
