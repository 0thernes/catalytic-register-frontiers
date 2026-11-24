module
-- SPDX-License-Identifier: Apache-2.0

public import Catalytic.CommRing
public import Catalytic.PrimeFieldTools
public import Catalytic.DigitSumDichotomy
public import Catalytic.ExtensionFieldSeparation
public import Catalytic.Pass2Soundness
public import Catalytic.BilinearFrobenius
public import Catalytic.ThreeRegisterBreakthrough
public import Catalytic.BalancedProduct

/-!
# Non-Vacuity Witnesses and Adversarial Sanity Checks

Exhibits concrete, non-trivial mathematical objects (`0 ≠ 1`) satisfying every
hypothesis bundle of Theorems `T1`–`T4`, together with positive and negative
small-case boundary evaluations. This ensures that none of the exported theorems
in `Challenge.lean` / `Solution.lean` hold vacuously over empty types or the zero ring.
-/

namespace Catalytic.NonVacuity

@[expose] public section

/-- Concrete finite modular ring `ℤ / pℤ` for any `p > 1` (zero-Mathlib witness). -/
structure ModP (p : Nat) (hp : 1 < p) where
  val : Nat
  lt : val < p

namespace ModP

theorem ext {p : Nat} {hp : 1 < p} {a b : ModP p hp} (h : a.val = b.val) : a = b := by
  cases a; cases b; cases h; rfl

instance (p : Nat) (hp : 1 < p) : DecidableEq (ModP p hp) := fun a b =>
  if h : a.val = b.val then isTrue (ext h) else isFalse (fun heq => h (congrArg ModP.val heq))

instance (p : Nat) (hp : 1 < p) : Zero (ModP p hp) := ⟨⟨0, by omega⟩⟩
instance (p : Nat) (hp : 1 < p) : One (ModP p hp) := ⟨⟨1, hp⟩⟩
instance (p : Nat) (hp : 1 < p) : Add (ModP p hp) :=
  ⟨fun a b => ⟨(a.val + b.val) % p, Nat.mod_lt _ (by omega)⟩⟩
instance (p : Nat) (hp : 1 < p) : Mul (ModP p hp) :=
  ⟨fun a b => ⟨(a.val * b.val) % p, Nat.mod_lt _ (by omega)⟩⟩
instance (p : Nat) (hp : 1 < p) : Neg (ModP p hp) :=
  ⟨fun a => ⟨(p - a.val) % p, Nat.mod_lt _ (by omega)⟩⟩

instance (p : Nat) (hp : 1 < p) : CRing (ModP p hp) where
  add_assoc a b c := by
    apply ext
    change ((a.val + b.val) % p + c.val) % p = (a.val + (b.val + c.val) % p) % p
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    rw [Nat.add_mod a.val ((b.val + c.val) % p), Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc]
  add_comm a b := by
    apply ext
    change (a.val + b.val) % p = (b.val + a.val) % p
    rw [Nat.add_comm]
  zero_add a := by
    apply ext
    change (0 + a.val) % p = a.val
    rw [Nat.zero_add, Nat.mod_eq_of_lt a.lt]
  add_neg a := by
    apply ext
    change (a.val + (p - a.val) % p) % p = 0
    have ha := a.lt
    by_cases h0 : a.val = 0
    · rw [h0, Nat.sub_zero, Nat.mod_self, Nat.add_zero, Nat.zero_mod]
    · have hlt : p - a.val < p := by omega
      rw [Nat.mod_eq_of_lt hlt]
      have hsum : a.val + (p - a.val) = p := by omega
      rw [hsum, Nat.mod_self]
  mul_assoc a b c := by
    apply ext
    change ((a.val * b.val) % p * c.val) % p = (a.val * ((b.val * c.val) % p)) % p
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
    rw [Nat.mul_mod a.val ((b.val * c.val) % p), Nat.mod_mod, ← Nat.mul_mod, Nat.mul_assoc]
  mul_comm a b := by
    apply ext
    change (a.val * b.val) % p = (b.val * a.val) % p
    rw [Nat.mul_comm]
  one_mul a := by
    apply ext
    change (1 * a.val) % p = a.val
    rw [Nat.one_mul, Nat.mod_eq_of_lt a.lt]
  left_distrib a b c := by
    apply ext
    change (a.val * ((b.val + c.val) % p)) % p = ((a.val * b.val) % p + (a.val * c.val) % p) % p
    rw [Nat.mul_mod a.val ((b.val + c.val) % p), Nat.mod_mod, ← Nat.mul_mod]
    rw [Nat.mul_add, Nat.add_mod]

theorem zero_ne_one (p : Nat) (hp : 1 < p) : (0 : ModP p hp) ≠ (1 : ModP p hp) := by
  intro h
  have hv := congrArg ModP.val h
  exact Nat.zero_ne_one hv

theorem natCast_val {p : Nat} {hp : 1 < p} (k : Nat) :
    (CRing.natCast k : ModP p hp).val = k % p := by
  induction k with
  | zero =>
    change 0 = 0 % p
    simp
  | succ n ih =>
    change ((CRing.natCast n : ModP p hp).val + 1) % p = (n + 1) % p
    rw [ih, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

theorem mul_intCast_lit_eq_one {p : Nat} {hp : 1 < p} (u : ModP p hp) (k : Nat)
    (z : Int) (hz : z = Int.ofNat k) (h : (u.val * (k % p)) % p = 1) :
    u * CRing.intCast z = (1 : ModP p hp) := by
  subst hz
  apply ext
  change (u.val * (CRing.natCast k : ModP p hp).val) % p = 1
  rw [natCast_val]
  exact h

theorem natCast_p_eq_zero (p : Nat) (hp : 1 < p) :
    (CRing.natCast p : ModP p hp) = (0 : ModP p hp) := by
  apply ext
  rw [natCast_val, Nat.mod_self]
  rfl

end ModP

/-- Concrete non-trivial `Char2CRing` witness: `𝔽_2 = ModP 2`. -/
abbrev F2 : Type := ModP 2 (by decide)

instance : Char2CRing F2 where
  add_self a := by
    apply ModP.ext
    change (a.val + a.val) % 2 = 0
    have hlt := a.lt
    omega

private theorem prime_2 : IsPrime 2 := ⟨by omega, fun d hd => by
  have hle : d ≤ 2 := Nat.le_of_dvd (by omega) hd
  rcases hd with ⟨q, hq⟩
  have : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases this with rfl | rfl | rfl <;> omega⟩

private theorem prime_3 : IsPrime 3 := ⟨by omega, fun d hd => by
  have hle : d ≤ 3 := Nat.le_of_dvd (by omega) hd
  rcases hd with ⟨q, hq⟩
  have : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl <;> omega⟩

private theorem prime_5 : IsPrime 5 := ⟨by omega, fun d hd => by
  have hle : d ≤ 5 := Nat.le_of_dvd (by omega) hd
  rcases hd with ⟨q, hq⟩
  have : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> omega⟩

private theorem prime_7 : IsPrime 7 := ⟨by omega, fun d hd => by
  have hle : d ≤ 7 := Nat.le_of_dvd (by omega) hd
  rcases hd with ⟨q, hq⟩
  have : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega⟩

/-- **Non-Vacuity Witness for T1:** concrete primes exist, with sharp positive and negative cases. -/
theorem nonvac_T1_witnesses :
    IsPrime 2 ∧ IsPrime 3 ∧ IsPrime 5 ∧ IsPrime 7 ∧
    InRPPass2 2 2 (monomial 4) ∧
    ¬ InRPPass2 2 10 (monomial 3) ∧
    InRPPass2 5 3 (monomial 2) ∧
    ¬ InRPPass2 5 2 (monomial 2) := by
  have hx4 : InRPPass2 2 2 (monomial 4) :=
    char_p_two_access_unbounded_degree 2 2 prime_2
  have hx3 : ¬ InRPPass2 2 10 (monomial 3) :=
    char_2_two_reg_x3_impossible 10
  have hx2_pos : InRPPass2 5 3 (monomial 2) :=
    (char_p_large_recovers_vinciguerra_thm35 5 2 3 prime_5 (by omega) (by omega) (by omega)).2 (by omega)
  have hx2_neg : ¬ InRPPass2 5 2 (monomial 2) := by
    intro h
    have := (char_p_large_recovers_vinciguerra_thm35 5 2 2 prime_5 (by omega) (by omega) (by omega)).1 h
    omega
  exact ⟨prime_2, prime_3, prime_5, prime_7, hx4, hx3, hx2_pos, hx2_neg⟩

/-- **Non-Vacuity Witness for T2:** `𝔽_2` is a non-trivial `Char2CRing` (`0 ≠ 1`) and `frobBilinProg 2`
cleanly adds `1^4 = 1 ≠ 0` to `R_0` while restoring `R_1, R_2`. -/
theorem nonvac_T2_witness :
    ((0 : F2) ≠ (1 : F2)) ∧
    let init : Fin 3 → F2 := fun i => if i.val = 1 then 1 else 0
    let final := BilinProg.exec (1 : F2) (frobBilinProg 2 (by omega)) init
    final ⟨0, by omega⟩ = 1 ∧ final ⟨1, by omega⟩ = 1 ∧ final ⟨2, by omega⟩ = 0 := by
  refine ⟨ModP.zero_ne_one 2 (by decide), ?_⟩
  have hclean := frobBilinProg_clean (R := F2) 2 (by omega) (1 : F2)
    (fun i : Fin 3 => if i.val = 1 then 1 else 0)
  have h0 := hclean.1
  have h1 := hclean.2 ⟨1, by omega⟩ (by decide)
  have h2 := hclean.2 ⟨2, by omega⟩ (by decide)
  refine ⟨?_, ?_, ?_⟩
  · rw [h0]; decide
  · rw [h1]; decide
  · rw [h2]; decide

/-- **Non-Vacuity Witness for T3a–T3d & T3g:** every denominator `D_5, D_6, D_7, D_8, D_9` is invertible
in an explicit non-trivial finite field (`0 ≠ 1`), namely `𝔽_5`, `𝔽_7`, `𝔽_11`, `𝔽_11`, `𝔽_11`. -/
theorem nonvac_T3_witnesses :
    (∃ (inv5 : ModP 5 (by decide)),
      (0 : ModP 5 (by decide)) ≠ 1 ∧ inv5 * CRing.intCast 576 = 1) ∧
    (∃ (inv6 : ModP 7 (by decide)),
      (0 : ModP 7 (by decide)) ≠ 1 ∧ inv6 * CRing.intCast 382500000 = 1) ∧
    (∃ (inv7 : ModP 11 (by decide)),
      (0 : ModP 11 (by decide)) ≠ 1 ∧ inv7 * CRing.intCast 68724637549388656012800 = 1) ∧
    (∃ (inv8 : ModP 11 (by decide)),
      (0 : ModP 11 (by decide)) ≠ 1 ∧ inv8 * CRing.intCast 2656207148788801777680 = 1) ∧
    (∃ (inv9 : ModP 11 (by decide)),
      (0 : ModP 11 (by decide)) ≠ 1 ∧
        inv9 * CRing.intCast 876702103804656272895371895753963647960420947968000 = 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨⟨1, by decide⟩, ModP.zero_ne_one 5 (by decide),
      ModP.mul_intCast_lit_eq_one ⟨1, by decide⟩ 576 576 rfl (by decide)⟩
  · exact ⟨⟨1, by decide⟩, ModP.zero_ne_one 7 (by decide),
      ModP.mul_intCast_lit_eq_one ⟨1, by decide⟩ 382500000 382500000 rfl (by decide)⟩
  · exact ⟨⟨8, by decide⟩, ModP.zero_ne_one 11 (by decide),
      ModP.mul_intCast_lit_eq_one ⟨8, by decide⟩ 68724637549388656012800 68724637549388656012800 rfl (by decide)⟩
  · exact ⟨⟨9, by decide⟩, ModP.zero_ne_one 11 (by decide),
      ModP.mul_intCast_lit_eq_one ⟨9, by decide⟩ 2656207148788801777680 2656207148788801777680 rfl (by decide)⟩
  · exact ⟨⟨9, by decide⟩, ModP.zero_ne_one 11 (by decide),
      ModP.mul_intCast_lit_eq_one ⟨9, by decide⟩
        876702103804656272895371895753963647960420947968000
        876702103804656272895371895753963647960420947968000 rfl (by decide)⟩

/-- **Non-Vacuity Witness for T4:** over `Int` (`0 ≠ 1`), `balancedProdProg` for `d = 2^2 = 4`
satisfies all preconditions of `T4`, has exact length `36`, cleanly evaluates
`st 0 + 1 * rangeProd xs 0 4`, and restores all three catalytic registers `1, 2, 3`. -/
theorem nonvac_T4_witness :
    ((0 : Int) ≠ (1 : Int)) ∧
    let xs : Nat → Int := fun i => ([2, 3, 5, 7] : List Int).getD i 0
    let st : Nat → Int := fun r => (r : Int) + 10
    let prog := balancedProdProg 2 0 1 [1, 2, 3] 0
    prog.length = 36 ∧
    CatProg.exec xs prog st 0 = 10 + rangeProd xs 0 4 ∧
    CatProg.exec xs prog st 1 = 11 ∧
    CatProg.exec xs prog st 2 = 12 ∧
    CatProg.exec xs prog st 3 = 13 := by
  have hnd : (0 :: [1, 2, 3]).Nodup := by decide
  have hclean := balancedProdProg_clean (R := Int) 2 0 1 [1, 2, 3] 0
    (Or.inr (by decide)) hnd
    (fun i => ([2, 3, 5, 7] : List Int).getD i 0)
    (fun r => (r : Int) + 10)
  have hlen : (balancedProdProg 2 0 1 [1, 2, 3] 0).length = 36 := by
    rw [balancedProdProg_length 2 0 1 [1, 2, 3] 0 (Or.inr (by decide))]
    have hf := balancedOpCount_formula 2
    omega
  refine ⟨by decide, hlen, ?_, ?_, ?_, ?_⟩
  · have h0 := congrFun hclean 0
    simpa [CRing.intCast_one, CRing.one_mul] using h0
  · have h1 := congrFun hclean 1
    simpa using h1
  · have h2 := congrFun hclean 2
    simpa using h2
  · have h3 := congrFun hclean 3
    simpa using h3

/-- Master non-vacuity witness bundling all theorem families (`T1`–`T4`, including `Pass2Soundness` char-`p`/`GF4` hom witnesses, `GF4` for `T1e`, and `D9` for `T3g`). -/
theorem nonvac_all_hypotheses :
    (IsPrime 2 ∧ IsPrime 3 ∧ IsPrime 5 ∧ IsPrime 7 ∧
      InRPPass2 2 2 (monomial 4) ∧ ¬ InRPPass2 2 10 (monomial 3) ∧
      InRPPass2 5 3 (monomial 2) ∧ ¬ InRPPass2 5 2 (monomial 2)) ∧
    ((CRing.natCast 5 : ModP 5 (by decide)) = 0) ∧
    ((GF4Hom.id.toFun .one : GF4) ≠ GF4Hom.id.toFun .z) ∧
    ((0 : F2) ≠ (1 : F2)) ∧
    (∃ inv5 : ModP 5 (by decide), inv5 * CRing.intCast 576 = 1) ∧
    (∃ inv6 : ModP 7 (by decide), inv6 * CRing.intCast 382500000 = 1) ∧
    (∃ inv7 : ModP 11 (by decide), inv7 * CRing.intCast 68724637549388656012800 = 1) ∧
    (∃ inv8 : ModP 11 (by decide), inv8 * CRing.intCast 2656207148788801777680 = 1) ∧
    (∃ inv9 : ModP 11 (by decide),
      inv9 * CRing.intCast 876702103804656272895371895753963647960420947968000 = 1) ∧
    ((0 : Int) ≠ (1 : Int)) := by
  rcases nonvac_T3_witnesses with ⟨⟨i5, _, h5⟩, ⟨i6, _, h6⟩, ⟨i7, _, h7⟩, ⟨i8, _, h8⟩, ⟨i9, _, h9⟩⟩
  exact ⟨nonvac_T1_witnesses, ModP.natCast_p_eq_zero 5 (by decide), GF4.one_ne_zero, nonvac_T2_witness.1,
    ⟨i5, h5⟩, ⟨i6, h6⟩, ⟨i7, h7⟩, ⟨i8, h8⟩, ⟨i9, h9⟩, nonvac_T4_witness.1⟩

end

end Catalytic.NonVacuity
