module
-- SPDX-License-Identifier: Apache-2.0

/-!
# Zero-Mathlib Commutative Ring and Field Primitives

Minimal self-contained algebraic structures used across `Catalytic.*` so that all
register-program theorems quantify over arbitrary commutative rings / fields with
zero external dependencies and only the three standard Lean axioms.
-/

namespace Catalytic

@[expose] public section

universe u

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

namespace CRing

variable {R : Type u} [CRing R]

@[simp] theorem add_zero (a : R) : a + 0 = a := by
  rw [add_comm, zero_add]

@[simp] theorem neg_add (a : R) : (-a) + a = 0 := by
  rw [add_comm, add_neg]

@[simp] theorem mul_one (a : R) : a * 1 = a := by
  rw [mul_comm, one_mul]

theorem right_distrib (a b c : R) : (a + b) * c = a * c + b * c := by
  rw [mul_comm, left_distrib, mul_comm c a, mul_comm c b]

theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  have h1 : (-a) + (a + b) = (-a) + (a + c) := congrArg ((-a) + ·) h
  rw [← add_assoc, ← add_assoc, neg_add, zero_add, zero_add] at h1
  exact h1

theorem add_right_cancel {a b c : R} (h : b + a = c + a) : b = c := by
  apply add_left_cancel (a := a)
  rw [add_comm a b, add_comm a c]
  exact h

@[simp] theorem mul_zero (a : R) : a * 0 = 0 := by
  apply add_left_cancel (a := a * 0)
  rw [← left_distrib, add_zero, add_zero]

@[simp] theorem zero_mul (a : R) : 0 * a = 0 := by
  rw [mul_comm, mul_zero]

theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  apply add_left_cancel (a := a)
  rw [add_neg, h]

@[simp] theorem neg_zero : -(0 : R) = 0 :=
  neg_eq_of_add_eq_zero (add_zero 0)

@[simp] theorem neg_neg (a : R) : -(-a) = a :=
  neg_eq_of_add_eq_zero (neg_add a)

theorem neg_add_rev (a b : R) : -(a + b) = (-a) + (-b) := by
  apply neg_eq_of_add_eq_zero
  calc
    (a + b) + ((-a) + (-b)) = (a + (-a)) + (b + (-b)) := by
      rw [add_assoc, ← add_assoc b (-a) (-b), add_comm b (-a), add_assoc (-a) b (-b), ← add_assoc]
    _ = 0 + 0 := by rw [add_neg, add_neg]
    _ = 0 := add_zero 0

theorem mul_neg (a b : R) : a * (-b) = -(a * b) := by
  symm
  apply neg_eq_of_add_eq_zero
  rw [← left_distrib, add_neg, mul_zero]

theorem neg_mul (a b : R) : (-a) * b = -(a * b) := by
  rw [mul_comm, mul_neg, mul_comm]

theorem neg_mul_neg (a b : R) : (-a) * (-b) = a * b := by
  rw [neg_mul, mul_neg, neg_neg]

def natCast : Nat → R
  | 0 => 0
  | n + 1 => natCast n + 1

def intCast : Int → R
  | Int.ofNat n => natCast n
  | Int.negSucc n => -(natCast (n + 1))

def pow (a : R) : Nat → R
  | 0 => 1
  | n + 1 => pow a n * a

@[simp] theorem natCast_zero : (natCast 0 : R) = 0 := rfl
@[simp] theorem natCast_one : (natCast 1 : R) = 1 := zero_add 1

theorem natCast_add (m n : Nat) : (natCast (m + n) : R) = natCast m + natCast n := by
  induction n with
  | zero => simp [natCast]
  | succ k ih =>
    change (natCast ((m + k) + 1) : R) = natCast m + (natCast k + 1)
    simp only [natCast, ih, add_assoc]

theorem natCast_mul (m n : Nat) : (natCast (m * n) : R) = natCast m * natCast n := by
  induction n with
  | zero => simp [natCast]
  | succ k ih =>
    rw [Nat.mul_succ, natCast_add, ih, natCast, left_distrib, mul_one]

@[simp] theorem intCast_zero : (intCast 0 : R) = 0 := rfl
@[simp] theorem intCast_one : (intCast 1 : R) = 1 := zero_add 1
@[simp] theorem intCast_neg_one : (intCast (-1) : R) = -(1 : R) := by
  change -(natCast 1 : R) = -(1 : R)
  rw [natCast_one]

theorem intCast_natCast (n : Nat) : (intCast (n : Int) : R) = natCast n := rfl

theorem intCast_neg (z : Int) : (intCast (-z) : R) = -(intCast z) := by
  cases z with
  | ofNat n =>
    cases n with
    | zero => simp [intCast]
    | succ k => rfl
  | negSucc n =>
    change (natCast (n + 1) : R) = -(-(natCast (n + 1) : R))
    rw [neg_neg]

private theorem intCast_subNat (a b : Nat) :
    (intCast ((a : Int) - (b : Int)) : R) = natCast a + -(natCast b) := by
  by_cases h : b ≤ a
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have h1 : ((b + d : Nat) : Int) - (b : Int) = (d : Int) := by omega
    rw [h1, intCast_natCast, natCast_add]
    calc
      (natCast d : R) = 0 + natCast d := (zero_add _).symm
      _ = (natCast b + -(natCast b)) + natCast d := by rw [add_neg]
      _ = natCast b + (-(natCast b) + natCast d) := add_assoc _ _ _
      _ = natCast b + (natCast d + -(natCast b)) := by rw [add_comm (-(natCast b)) (natCast d)]
      _ = (natCast b + natCast d) + -(natCast b) := (add_assoc _ _ _).symm
  · have hlt : a < b := Nat.lt_of_not_le h
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hlt
    have hb : b = a + (d + 1) := by omega
    have h1 : (a : Int) - (b : Int) = Int.negSucc d := by omega
    rw [h1]
    change -(natCast (d + 1) : R) = natCast a + -(natCast b)
    rw [hb, natCast_add a (d + 1), neg_add_rev]
    calc
      -(natCast (d + 1) : R) = 0 + -(natCast (d + 1)) := (zero_add _).symm
      _ = (natCast a + -(natCast a)) + -(natCast (d + 1)) := by rw [add_neg]
      _ = natCast a + (-(natCast a) + -(natCast (d + 1))) := add_assoc _ _ _

theorem intCast_add (x y : Int) : (intCast (x + y) : R) = intCast x + intCast y := by
  cases x with
  | ofNat a =>
    cases y with
    | ofNat b =>
      change (natCast (a + b) : R) = natCast a + natCast b
      exact natCast_add a b
    | negSucc b =>
      have heq : Int.ofNat a + Int.negSucc b = (a : Int) - ((b + 1 : Nat) : Int) := by
        change (a : Int) + (-((b + 1 : Nat) : Int)) = (a : Int) - ((b + 1 : Nat) : Int)
        omega
      rw [heq, intCast_subNat a (b + 1)]
      rfl
  | negSucc a =>
    cases y with
    | ofNat b =>
      have heq : Int.negSucc a + Int.ofNat b = (b : Int) - ((a + 1 : Nat) : Int) := by
        change (-((a + 1 : Nat) : Int)) + (b : Int) = (b : Int) - ((a + 1 : Nat) : Int)
        omega
      rw [heq, intCast_subNat b (a + 1), add_comm]
      rfl
    | negSucc b =>
      have heq : Int.negSucc a + Int.negSucc b = Int.negSucc (a + b + 1) := rfl
      rw [heq]
      change -(natCast (a + b + 2) : R) = -(natCast (a + 1)) + -(natCast (b + 1))
      have h2 : a + b + 2 = (a + 1) + (b + 1) := by omega
      rw [h2, natCast_add, neg_add_rev]

theorem intCast_mul (x y : Int) : (intCast (x * y) : R) = intCast x * intCast y := by
  cases x with
  | ofNat a =>
    cases y with
    | ofNat b =>
      change (natCast (a * b) : R) = natCast a * natCast b
      exact natCast_mul a b
    | negSucc b =>
      have heq : Int.ofNat a * Int.negSucc b = -((a * (b + 1) : Nat) : Int) := by
        rw [Int.ofNat_eq_natCast, Int.negSucc_eq, Int.mul_neg, ← Int.natCast_succ, ← Int.natCast_mul]
      rw [heq, intCast_neg, intCast_natCast, natCast_mul]
      change -(natCast a * natCast (b + 1) : R) = natCast a * -(natCast (b + 1))
      rw [mul_neg]
  | negSucc a =>
    cases y with
    | ofNat b =>
      have heq : Int.negSucc a * Int.ofNat b = -(((a + 1) * b : Nat) : Int) := by
        rw [Int.ofNat_eq_natCast, Int.negSucc_eq, Int.neg_mul, ← Int.natCast_succ, ← Int.natCast_mul]
      rw [heq, intCast_neg, intCast_natCast, natCast_mul]
      change -(natCast (a + 1) * natCast b : R) = -(natCast (a + 1)) * natCast b
      rw [neg_mul]
    | negSucc b =>
      have heq : Int.negSucc a * Int.negSucc b = (((a + 1) * (b + 1) : Nat) : Int) := by
        rw [Int.negSucc_eq, Int.negSucc_eq, Int.neg_mul_neg, ← Int.natCast_succ, ← Int.natCast_succ, ← Int.natCast_mul]
      rw [heq, intCast_natCast, natCast_mul]
      change (natCast (a + 1) * natCast (b + 1) : R) = -(natCast (a + 1)) * -(natCast (b + 1))
      rw [neg_mul_neg]

@[simp] theorem pow_zero (a : R) : pow a 0 = 1 := rfl
@[simp] theorem pow_one (a : R) : pow a 1 = a := one_mul a

theorem pow_add (a : R) (m n : Nat) : pow a (m + n) = pow a m * pow a n := by
  induction n with
  | zero => simp [pow]
  | succ k ih =>
    change pow a ((m + k) + 1) = pow a m * (pow a k * a)
    simp only [pow, ih, mul_assoc]

theorem pow_mul (a : R) (m n : Nat) : pow a (m * n) = pow (pow a m) n := by
  induction n with
  | zero => simp [pow]
  | succ k ih =>
    rw [Nat.mul_succ, pow_add, ih, pow]

theorem mul_pow (a b : R) (n : Nat) : pow (a * b) n = pow a n * pow b n := by
  induction n with
  | zero => simp [pow]
  | succ k ih =>
    simp only [pow, ih]
    calc
      (pow a k * pow b k) * (a * b)
          = pow a k * (pow b k * (a * b)) := mul_assoc _ _ _
      _   = pow a k * ((pow b k * a) * b) := by rw [← mul_assoc (pow b k) a b]
      _   = pow a k * ((a * pow b k) * b) := by rw [mul_comm (pow b k) a]
      _   = pow a k * (a * (pow b k * b)) := by rw [mul_assoc a (pow b k) b]
      _   = (pow a k * a) * (pow b k * b) := (mul_assoc _ _ _).symm

end CRing

/-- Characteristic-2 commutative ring (e.g. `F_2`, `F_{2^m}`, `F_2[x, c_0, ..., c_k]`). -/
class Char2CRing (R : Type u) extends CRing R where
  add_self : ∀ a : R, a + a = 0

namespace Char2CRing

variable {R : Type u} [Char2CRing R]

theorem neg_eq_self (a : R) : -a = a :=
  CRing.neg_eq_of_add_eq_zero (add_self a)

/-- Freshman's Dream: `(a + b)^2 = a^2 + b^2` in any characteristic-2 commutative ring. -/
theorem add_sq (a b : R) : (a + b) * (a + b) = a * a + b * b := by
  calc
    (a + b) * (a + b)
        = (a + b) * a + (a + b) * b := CRing.left_distrib _ _ _
    _   = (a * a + b * a) + (a * b + b * b) := by rw [CRing.right_distrib, CRing.right_distrib]
    _   = a * a + ((b * a + a * b) + b * b) := by rw [CRing.add_assoc, ← CRing.add_assoc (b * a)]
    _   = a * a + ((a * b + a * b) + b * b) := by rw [CRing.mul_comm b a]
    _   = a * a + (0 + b * b) := by rw [add_self]
    _   = a * a + b * b := by rw [CRing.zero_add]

theorem add_pow_two_pow (a b : R) (k : Nat) :
    CRing.pow (a + b) (2 ^ k) = CRing.pow a (2 ^ k) + CRing.pow b (2 ^ k) := by
  induction k with
  | zero => simp
  | succ m ih =>
    have hpow : ∀ z : R, CRing.pow z (2 ^ (m + 1)) = CRing.pow z (2 ^ m) * CRing.pow z (2 ^ m) := by
      intro z
      have h2 : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by omega
      rw [h2, CRing.pow_add]
    rw [hpow (a + b), ih, add_sq, ← hpow a, ← hpow b]

end Char2CRing

/-- Standard `Int` instance of `CRing`. -/
instance : CRing Int where
  add_assoc := Int.add_assoc
  add_comm := Int.add_comm
  zero_add := Int.zero_add
  add_neg := Int.add_right_neg
  mul_assoc := Int.mul_assoc
  mul_comm := Int.mul_comm
  one_mul := Int.one_mul
  left_distrib := Int.mul_add

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

theorem mul_natCast_eq_one {p : Nat} {hp : 1 < p} (u : ModP p hp) (k : Nat)
    (h : (u.val * (k % p)) % p = 1) :
    u * CRing.natCast k = (1 : ModP p hp) := by
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

end

end Catalytic
