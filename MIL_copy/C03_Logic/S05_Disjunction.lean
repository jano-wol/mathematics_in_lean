import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  · rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  . rw [abs_of_nonneg h]
  . rw [abs_of_neg h]
    linarith [h]


theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  . rw [abs_of_nonneg h]
    linarith [h]
  . rw [abs_of_neg h]


theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rcases le_or_gt 0 (x + y) with h | h
  . calc
      |x + y| = x + y := by rw [abs_of_nonneg h]
      _ ≤ |x| + y := by rel [le_abs_self x]
      _ ≤ |x| + |y| := by rel [le_abs_self y]
  . calc
      |x + y| = -(x + y) := by rw [abs_of_neg h]
      _ = -x + (- y) := by ring
      _ ≤ |x| + (- y) := by rel [neg_le_abs_self x]
      _ ≤ |x| + |y| := by rel [neg_le_abs_self y]

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  constructor
  intro i
  rcases le_or_gt 0 (y) with h | h
  rw [abs_of_nonneg h] at i
  left
  apply i
  rw [abs_of_neg h] at i
  right
  apply i
  intro i
  obtain i | i := i
  linarith [le_abs_self y]
  linarith [neg_le_abs_self y]


theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  constructor
  intro i
  constructor
  linarith [neg_le_abs_self x]
  linarith [le_abs_self x]
  intro i
  rcases i with ⟨i1, i2⟩
  rcases le_or_gt 0 (x) with h | h
  rw [abs_of_nonneg h]
  apply i2
  rw [abs_of_neg h]
  linarith [i1]


end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  · right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  · rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨x, ⟨y, h1 | h1⟩⟩ <;> linarith [h1, pow_two_nonneg x, pow_two_nonneg y]


example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h2 : (x - 1) * (x + 1) = 0 := by linarith [h]
  apply eq_zero_or_eq_zero_of_mul_eq_zero at h2
  rcases h2 with h2 | h2
  left
  linarith [h2]
  right
  linarith [h2]

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h2 : (x - y) * (x + y) = 0 := by linarith [h]
  apply eq_zero_or_eq_zero_of_mul_eq_zero at h2
  rcases h2 with h2 | h2
  left
  linarith [h2]
  right
  linarith [h2]

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h2 : (x - 1) * (x + 1) = 0 := by
    calc
      (x - 1) * (x + 1) = x ^ 2 - 1 := by ring
      _ = 1 - 1:= by rw [h]
      _ = 0 := by ring
  apply eq_zero_or_eq_zero_of_mul_eq_zero at h2
  rcases h2 with h2 | h2
  left
  calc
    x = (x - 1) + 1 := by ring
    _ = 0 + 1 := by rw [h2]
    _ = 1 := by ring
  right
  calc
    x = (x + 1) - 1 := by ring
    _ = 0 - 1 := by rw [h2]
    _ = -1 := by ring

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h2 : (x - y) * (x + y) = 0 := by
    calc
      (x - y) * (x + y) = x ^ 2 - y ^ 2 := by ring
      _ = y ^ 2 - y ^ 2 := by rw [h]
      _ = 0 := by ring
  apply eq_zero_or_eq_zero_of_mul_eq_zero at h2
  rcases h2 with h2 | h2
  left
  calc
    x = (x - y) + y := by ring
    _ = 0 + y := by rw [h2]
    _ = y := by ring
  right
  calc
    x = (x + y) - y := by ring
    _ = 0 - y := by rw [h2]
    _ = -y := by ring

end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  · contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor
  intro i
  by_cases hQ : Q
  . right
    apply hQ
  . by_cases hP : P
    . have h2 := i hP
      right
      apply h2
    left
    apply hP
  intro i
  rcases i with i | i
  intro j
  contradiction
  intro _
  apply i
