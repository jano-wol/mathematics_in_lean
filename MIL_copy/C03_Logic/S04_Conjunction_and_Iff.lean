import MIL.Common
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime.Basic

namespace C03S04

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y := by
  constructor
  · assumption
  intro h
  apply h₁
  rw [h]

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y :=
  ⟨h₀, fun h ↦ h₁ (by rw [h])⟩

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y :=
  have h : x ≠ y := by
    contrapose! h₁
    rw [h₁]
  ⟨h₀, h⟩

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  rcases h with ⟨h₀, h₁⟩
  contrapose! h₁
  exact le_antisymm h₀ h₁

example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬y ≤ x := by
  rintro ⟨h₀, h₁⟩ h'
  exact h₁ (le_antisymm h₀ h')

example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬y ≤ x :=
  fun ⟨h₀, h₁⟩ h' ↦ h₁ (le_antisymm h₀ h')

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  have ⟨h₀, h₁⟩ := h
  contrapose! h₁
  exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  cases h
  case intro h₀ h₁ =>
    contrapose! h₁
    exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  cases h
  next h₀ h₁ =>
    contrapose! h₁
    exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  match h with
    | ⟨h₀, h₁⟩ =>
        contrapose! h₁
        exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  intro h'
  apply h.right
  exact le_antisymm h.left h'

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x :=
  fun h' ↦ h.right (le_antisymm h.left h')

theorem div_le {m n : ℕ} (h : m ∣ n) : m ≤ n ∨ n = 0 := by
  obtain ⟨k, hk⟩ := h
  have h2 := le_or_gt k 0
  obtain h2 | h2 := h2
  have h3 : k = 0 := by linarith
  have h4 : n = 0 := by
    calc
      n = m * k := hk
      _ = m * 0 := by rw [h3]
      _ = 0 := by ring
  right
  apply h4
  have h5 : m ≤ m * k := by exact Nat.le_mul_of_pos_right m h2
  left
  calc
    m ≤ m * k := h5
    _ ≤ n := by rw [hk]

theorem div_zero {n : ℕ} (h : 0 ∣ n) : n = 0 := by
  obtain ⟨k, hk⟩ := h
  calc
    n = 0 * k := hk
    _ = 0 := by ring

example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) : m ∣ n ∧ ¬n ∣ m := by
  obtain ⟨h1, h2⟩ := h
  constructor
  apply h1
  contrapose! h2
  have h3 := div_le h1
  have h4 := div_le h2
  obtain h3 | h3 := h3
  obtain h4 | h4 := h4
  apply le_antisymm
  apply h3
  apply h4
  rw [h4] at h1
  have h5 := div_zero h1
  rw [h4, h5]
  obtain h4 | h4 := h4
  rw [h3] at h2
  have h5 := div_zero h2
  rw [h3, h5]
  rw [h3, h4]




example : ∃ x : ℝ, 2 < x ∧ x < 4 :=
  ⟨5 / 2, by norm_num, by norm_num⟩

example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y := by
  rintro ⟨z, xltz, zlty⟩
  exact lt_trans xltz zlty

example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y :=
  fun ⟨_, xltz, zlty⟩ ↦ lt_trans xltz zlty

example : ∃ x : ℝ, 2 < x ∧ x < 4 := by
  use 5 / 2
  constructor <;> norm_num

example : ∃ m n : ℕ, 4 < m ∧ m < n ∧ n < 10 ∧ Nat.Prime m ∧ Nat.Prime n := by
  use 5
  use 7
  norm_num

example {x y : ℝ} : x ≤ y ∧ x ≠ y → x ≤ y ∧ ¬y ≤ x := by
  rintro ⟨h₀, h₁⟩
  use h₀
  exact fun h' ↦ h₁ (le_antisymm h₀ h')

example {x y : ℝ} (h : x ≤ y) : ¬y ≤ x ↔ x ≠ y := by
  constructor
  · contrapose!
    rintro rfl
    rfl
  contrapose!
  exact le_antisymm h

example {x y : ℝ} (h : x ≤ y) : ¬y ≤ x ↔ x ≠ y :=
  ⟨fun h₀ h₁ ↦ h₀ (by rw [h₁]), fun h₀ h₁ ↦ h₀ (le_antisymm h h₁)⟩

example {x y : ℝ} : x ≤ y ∧ ¬y ≤ x ↔ x ≤ y ∧ x ≠ y := by
  constructor
  intro ⟨h1, h2⟩
  constructor
  apply h1
  contrapose! h2
  rw [h2]
  intro h
  obtain ⟨h1, h2⟩ := h
  constructor
  apply h1
  contrapose! h2
  apply le_antisymm
  apply h1
  apply h2



theorem aux {x y : ℝ} (h : x ^ 2 + y ^ 2 = 0) : x = 0 :=
  have h' : x ^ 2 = 0 := by
    have h2 := pow_two_nonneg x
    have h3 : x ^ 2 = 0 ∨ x ^ 2 > 0 := by exact Or.symm (LE.le.gt_or_eq h2)
    obtain h3 | h3 := h3
    apply h3
    have h4 : (0 : ℝ)  > 0 := by
      calc
        (0 : ℝ)  = x ^ 2 + y ^ 2 := by rw [h]
        _ > 0 + y ^ 2 := by rel[h3]
        _ = y ^ 2 := by ring
        _ ≥ 0 := pow_two_nonneg y
    norm_num at h4
  pow_eq_zero h'

example (x y : ℝ) : x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  intro h
  constructor
  apply aux h
  have h2 : y ^ 2 + x ^ 2 = 0 := by linarith [h]
  apply aux h2
  intro ⟨h3, h4⟩
  calc
    x ^ 2 + y ^ 2 = 0 ^ 2 + 0 ^ 2 := by rw [h3, h4]
    _ = 0 := by ring

section

example (x : ℝ) : |x + 3| < 5 → -8 < x ∧ x < 2 := by
  rw [abs_lt]
  intro h
  constructor <;> linarith

example : 3 ∣ Nat.gcd 6 15 := by
  rw [Nat.dvd_gcd_iff]
  constructor <;> norm_num

end

theorem not_monotone_iff {f : ℝ → ℝ} : ¬Monotone f ↔ ∃ x y, x ≤ y ∧ f x > f y := by
  rw [Monotone]
  push_neg
  rfl

example : ¬Monotone fun x : ℝ ↦ -x := by
  dsimp [Monotone] at *
  push_neg
  use 0, 1
  constructor <;> norm_num


section
variable {α : Type*} [PartialOrder α]
variable (a b : α)

example : a < b ↔ a ≤ b ∧ a ≠ b := by
  rw [lt_iff_le_not_le]
  constructor
  intro h
  obtain ⟨h1, h2⟩ := h
  constructor
  apply h1
  contrapose! h2
  rw [h2]
  intro h
  obtain ⟨h1, h2⟩ := h
  constructor
  apply h1
  contrapose! h2
  apply le_antisymm
  apply h1
  apply h2

end

section
variable {α : Type*} [Preorder α]
variable (a b c : α)

example : ¬a < a := by
  rw [lt_iff_le_not_le]
  push_neg
  exact fun a => a



example : a < b → b < c → a < c := by
  intro h1 h2
  calc
    a < b := h1
    _ < c := h2

end
