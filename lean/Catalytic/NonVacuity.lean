module
-- SPDX-License-Identifier: Apache-2.0

public import Catalytic.CommRing
public import Catalytic.PrimeFieldTools
public import Catalytic.DigitSumDichotomy
public import Catalytic.ExtensionFieldSeparation
public import Catalytic.Pass2Soundness
public import Catalytic.BilinearFrobenius
public import Catalytic.ThreeRegisterBreakthrough
public import Catalytic.FourRegisterPowering
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

/-- Concrete non-trivial `Char2CRing` witness: `𝔽_2 = ModP 2` (from `Catalytic.CommRing`). -/
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

/-- **Non-Vacuity Witness for T3h (4-Register Powering):** concrete non-trivial finite fields
`𝔽_13` (`N = 20`, `ℓ = 1`, `D_8`, `12!`, `2!` all invertible) and `𝔽_7` (`N = 20`, `ℓ = 1`,
`6!`, `2!` invertible) satisfy every hypothesis of `four_reg_powering_x13` and `four_reg_powering_x7`. -/
theorem nonvac_T3h_witnesses :
    (∃ (invD8 inv12 inv2 : ModP 13 (by decide)),
      (0 : ModP 13 (by decide)) ≠ 1 ∧
      invD8 * CRing.intCast 2656207148788801777680 = 1 ∧
      inv12 * CRing.natCast (fact 12) = 1 ∧
      inv2 * CRing.natCast (fact (baseDigits 13 (by decide) 20).length) = 1) ∧
    (∃ (inv6 inv2 : ModP 7 (by decide)),
      (0 : ModP 7 (by decide)) ≠ 1 ∧
      inv6 * CRing.natCast (fact 6) = 1 ∧
      inv2 * CRing.natCast (fact (baseDigits 7 (by decide) 20).length) = 1) := by
  have hlen13 : (baseDigits 13 (by decide) 20).length = 2 := by
    unfold baseDigits; simp; unfold baseDigits; simp
  have hlen7 : (baseDigits 7 (by decide) 20).length = 2 := by
    unfold baseDigits; simp; unfold baseDigits; simp
  refine ⟨⟨⟨10, by decide⟩, ⟨12, by decide⟩, ⟨7, by decide⟩, ModP.zero_ne_one 13 (by decide), ?_, ?_, ?_⟩,
          ⟨⟨6, by decide⟩, ⟨4, by decide⟩, ModP.zero_ne_one 7 (by decide), ?_, ?_⟩⟩
  · exact ModP.mul_intCast_lit_eq_one ⟨10, by decide⟩
      2656207148788801777680 2656207148788801777680 rfl (by decide)
  · exact ModP.mul_natCast_eq_one ⟨12, by decide⟩ (fact 12) (by decide)
  · rw [hlen13]
    exact ModP.mul_natCast_eq_one ⟨7, by decide⟩ (fact 2) (by decide)
  · exact ModP.mul_natCast_eq_one ⟨6, by decide⟩ (fact 6) (by decide)
  · rw [hlen7]
    exact ModP.mul_natCast_eq_one ⟨4, by decide⟩ (fact 2) (by decide)

/-- **Non-Vacuity Witness for T3i (Streaming Frequency Moments over `R^n`):**
Over the non-trivial product ring `Fin 3 → 𝔽_13` (`0 ≠ 1`), `four_reg_streaming_moment_x13`
instantiates cleanly at `n = 3, D = 20` (`ℓ = 1`), yielding a literal passive 4-vector-register
program with `3 * accesses < 104 * 8^1` whose coordinate sum computes `F_20(f) = ∑_{i<3} f_i^20`. -/
theorem nonvac_T3i_witness :
    ((0 : Fin 3 → ModP 13 (by decide)) ≠ (1 : Fin 3 → ModP 13 (by decide))) ∧
    ∃ prog : List (Pass4Instr (Fin 3 → ModP 13 (by decide))),
      3 * Pass4Prog.accesses prog < 104 * 8 ^ 1 ∧
      ∀ f o u r1 r2 : Fin 3 → ModP 13 (by decide),
        let res := Pass4Prog.exec f prog (o, u, r1, r2)
        (∀ i : Fin 3, res.1 i = o i + CRing.pow (f i) 20) ∧
        res.2 = (u, r1, r2) ∧
        sumFin res.1 = sumFin o + sumFin (fun i => CRing.pow (f i) 20) := by
  refine ⟨fun h => ModP.zero_ne_one 13 (by decide) (congrFun h ⟨0, by decide⟩), ?_⟩
  rcases nonvac_T3h_witnesses.1 with ⟨iD8, i12, i2, _, hD8, h12, h2⟩
  have hlen13 : (baseDigits 13 (by decide) 20).length = 2 := by
    unfold baseDigits; simp; unfold baseDigits; simp
  rcases four_reg_streaming_moment_x13 (R := ModP 13 (by decide)) 3 20 (by omega)
      iD8 i12 i2 hD8 h12 h2 with ⟨prog, _, hacc, hclean⟩
  rw [hlen13] at hacc
  exact ⟨prog, hacc, hclean⟩

/-- **Non-Vacuity Witness for T1sc (`Pass2Soundness` over bivariate `FPS`):**
Exhibits `FPS (FPS (ModP 5))` as a concrete non-trivial (`0 ≠ 1`) characteristic-`5` commutative
ring and instantiates `pass2_clean_iff_ring_exec` on `x^2` (`p = 5, t = 3`), yielding a literal
`≤ 3`-access `Pass2Prog` cleanly computing `x^2` over every characteristic-`5` commutative ring. -/
theorem nonvac_T1sc_witness :
    ((0 : FPS (FPS (ModP 5 (by decide)))) ≠ (1 : FPS (FPS (ModP 5 (by decide))))) ∧
    ((CRing.natCast 5 : FPS (FPS (ModP 5 (by decide)))) = 0) ∧
    ∃ prog : List Pass2Instr,
      Pass2Prog.accesses prog ≤ 3 ∧
      ∀ (R : Type) [CRing R], (CRing.natCast 5 : R) = 0 →
        ∀ o u x : R, Pass2Prog.execRing x prog (o, u) = (o + evalPolyR (monomial 2) x, u) := by
  have hne : (0 : FPS (FPS (ModP 5 (by decide)))) ≠ 1 := by
    intro h
    have hc := congrArg (fun s : FPS (FPS (ModP 5 (by decide))) => (s.coeff 0).coeff 0) h
    exact ModP.zero_ne_one 5 (by decide) hc
  have hchar : (CRing.natCast 5 : FPS (FPS (ModP 5 (by decide)))) = 0 := by
    rw [FPS.natCast_eq, FPS.natCast_eq, ModP.natCast_p_eq_zero 5 (by decide),
        FPS.const_zero, FPS.const_zero]
  rcases nonvac_T1_witnesses.2.2.2.2.2.2.1 with ⟨prog, hacc, hclean⟩
  exact ⟨hne, hchar, prog, hacc, (pass2_clean_iff_ring_exec (by decide) prog (monomial 2)).1 hclean⟩

/-- **Non-Vacuity Witness for T1esc (`Pass2Soundness` over bivariate `FPS (FPS GF4)`):**
Exhibits `FPS (FPS GF4)` as a concrete non-trivial (`0 ≠ 1`) commutative `GF4`-algebra and
instantiates `pass2gf4_clean_iff_alg_exec` on `x^3` (`gf4_x3_in_4_accesses`), yielding a literal
`≤ 4`-access `Pass2GF4Prog` cleanly computing `x^3` over every commutative `GF4`-algebra. -/
theorem nonvac_T1esc_witness :
    ((0 : FPS (FPS GF4)) ≠ (1 : FPS (FPS GF4))) ∧
    ∃ prog : List Pass2GF4Instr,
      Pass2GF4Prog.accesses prog ≤ 4 ∧
      ∀ (R : Type) [CRing R] (φ : GF4Hom R) (o u x : R),
        Pass2GF4Prog.execAlg φ x prog (o, u) = (o + evalPolyGF4Alg φ (monomialGF4 3) x, u) := by
  have hne : (0 : FPS (FPS GF4)) ≠ 1 := by
    intro h
    have hc := congrArg (fun s : FPS (FPS GF4) => (s.coeff 0).coeff 0) h
    exact GF4.one_ne_zero hc.symm
  rcases gf4_x3_in_4_accesses with ⟨prog, hacc, hclean⟩
  exact ⟨hne, prog, hacc, (pass2gf4_clean_iff_alg_exec prog (monomialGF4 3)).1 hclean⟩

/-- Master non-vacuity witness bundling all theorem families (`T1`–`T4`, including `Pass2Soundness`
char-`p`/`GF4` hom witnesses and bivariate `FPS (FPS _)` witnesses for `T1sc`/`T1esc`, `GF4` for
`T1e`, `D9` for `T3g`, 4-register powering for `T3h`, and concrete product-ring `Fin 3 → 𝔽_13`
streaming frequency moments for `T3i`). -/
theorem nonvac_all_hypotheses :
    (IsPrime 2 ∧ IsPrime 3 ∧ IsPrime 5 ∧ IsPrime 7 ∧
      InRPPass2 2 2 (monomial 4) ∧ ¬ InRPPass2 2 10 (monomial 3) ∧
      InRPPass2 5 3 (monomial 2) ∧ ¬ InRPPass2 5 2 (monomial 2)) ∧
    ((CRing.natCast 5 : ModP 5 (by decide)) = 0) ∧
    ((GF4Hom.id.toFun .one : GF4) ≠ GF4Hom.id.toFun .z) ∧
    ((0 : FPS (FPS (ModP 5 (by decide)))) ≠ (1 : FPS (FPS (ModP 5 (by decide)))) ∧
      (CRing.natCast 5 : FPS (FPS (ModP 5 (by decide)))) = 0 ∧
      ∃ prog : List Pass2Instr, Pass2Prog.accesses prog ≤ 3 ∧
        ∀ (R : Type) [CRing R], (CRing.natCast 5 : R) = 0 →
          ∀ o u x : R, Pass2Prog.execRing x prog (o, u) = (o + evalPolyR (monomial 2) x, u)) ∧
    ((0 : FPS (FPS GF4)) ≠ (1 : FPS (FPS GF4)) ∧
      ∃ prog : List Pass2GF4Instr, Pass2GF4Prog.accesses prog ≤ 4 ∧
        ∀ (R : Type) [CRing R] (φ : GF4Hom R) (o u x : R),
          Pass2GF4Prog.execAlg φ x prog (o, u) = (o + evalPolyGF4Alg φ (monomialGF4 3) x, u)) ∧
    ((0 : F2) ≠ (1 : F2)) ∧
    (∃ inv5 : ModP 5 (by decide), inv5 * CRing.intCast 576 = 1) ∧
    (∃ inv6 : ModP 7 (by decide), inv6 * CRing.intCast 382500000 = 1) ∧
    (∃ inv7 : ModP 11 (by decide), inv7 * CRing.intCast 68724637549388656012800 = 1) ∧
    (∃ inv8 : ModP 11 (by decide), inv8 * CRing.intCast 2656207148788801777680 = 1) ∧
    (∃ inv9 : ModP 11 (by decide),
      inv9 * CRing.intCast 876702103804656272895371895753963647960420947968000 = 1) ∧
    (∃ (invD8 inv12 inv2 : ModP 13 (by decide)),
      invD8 * CRing.intCast 2656207148788801777680 = 1 ∧
      inv12 * CRing.natCast (fact 12) = 1 ∧
      inv2 * CRing.natCast (fact (baseDigits 13 (by decide) 20).length) = 1) ∧
    ((0 : Fin 3 → ModP 13 (by decide)) ≠ (1 : Fin 3 → ModP 13 (by decide)) ∧
      ∃ prog : List (Pass4Instr (Fin 3 → ModP 13 (by decide))),
        3 * Pass4Prog.accesses prog < 104 * 8 ^ 1 ∧
        ∀ f o u r1 r2 : Fin 3 → ModP 13 (by decide),
          let res := Pass4Prog.exec f prog (o, u, r1, r2)
          (∀ i : Fin 3, res.1 i = o i + CRing.pow (f i) 20) ∧
          res.2 = (u, r1, r2) ∧
          sumFin res.1 = sumFin o + sumFin (fun i => CRing.pow (f i) 20)) ∧
    ((0 : Int) ≠ (1 : Int)) := by
  rcases nonvac_T3_witnesses with ⟨⟨i5, _, h5⟩, ⟨i6, _, h6⟩, ⟨i7, _, h7⟩, ⟨i8, _, h8⟩, ⟨i9, _, h9⟩⟩
  rcases nonvac_T3h_witnesses.1 with ⟨iD8, i12, i2, _, hD8, h12, h2⟩
  exact ⟨nonvac_T1_witnesses, ModP.natCast_p_eq_zero 5 (by decide), GF4.one_ne_zero,
    nonvac_T1sc_witness, nonvac_T1esc_witness, nonvac_T2_witness.1,
    ⟨i5, h5⟩, ⟨i6, h6⟩, ⟨i7, h7⟩, ⟨i8, h8⟩, ⟨i9, h9⟩, ⟨iD8, i12, i2, hD8, h12, h2⟩,
    nonvac_T3i_witness, nonvac_T4_witness.1⟩

end

end Catalytic.NonVacuity
