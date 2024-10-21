import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Prime.Basic
import MIL.Common

section
variable {α : Type*}
variable (s t u : Set α)
open Set

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def, inter_def, inter_def]
  rw [subset_def] at h
  simp only [mem_setOf]
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  simp only [subset_def, mem_inter_iff] at *
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro x xsu
  exact ⟨h xsu.1, xsu.2⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  fun _ ⟨xs, xu⟩ ↦ ⟨h xs, xu⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  intro x hx
  have xs : x ∈ s := hx.1
  have xtu : x ∈ t ∪ u := hx.2
  rcases xtu with xt | xu
  · left
    show x ∈ s ∩ t
    exact ⟨xs, xt⟩
  · right
    show x ∈ s ∩ u
    exact ⟨xs, xu⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rintro x ⟨xs, xt | xu⟩
  · left; exact ⟨xs, xt⟩
  · right; exact ⟨xs, xu⟩

example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  rintro x hx
  rcases hx with ⟨xl, xr⟩ | ⟨xl, xr⟩
  . have h : x ∈ t ∪ u := by
      apply mem_union_left
      apply xr
    exact ⟨xl, h⟩
  . have h : x ∈ t ∪ u := by
      apply mem_union_right
      apply xr
    exact ⟨xl, h⟩


example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  intro x xstu
  have xs : x ∈ s := xstu.1.1
  have xnt : x ∉ t := xstu.1.2
  have xnu : x ∉ u := xstu.2
  constructor
  · exact xs
  intro xtu
  -- x ∈ t ∨ x ∈ u
  rcases xtu with xt | xu
  · show False; exact xnt xt
  · show False; exact xnu xu

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  rintro x ⟨⟨xs, xnt⟩, xnu⟩
  use xs
  rintro (xt | xu) <;> contradiction

example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  rintro x ⟨xs, xnu⟩
  have xnt : x ∉ t := by
    by_contra r
    have h2 : x ∈ t ∪ u := by
      apply mem_union_left
      apply r
    contradiction
  have xnu : x ∉ u := by
    by_contra r
    have h2 : x ∈ t ∪ u := by
      apply mem_union_right
      apply r
    contradiction
  constructor
  constructor
  apply xs
  apply xnt
  apply xnu



example : s ∩ t = t ∩ s := by
  ext x
  simp only [mem_inter_iff]
  constructor
  · rintro ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro ⟨xt, xs⟩; exact ⟨xs, xt⟩

example : s ∩ t = t ∩ s :=
  Set.ext fun _ ↦ ⟨fun ⟨xs, xt⟩ ↦ ⟨xt, xs⟩, fun ⟨xt, xs⟩ ↦ ⟨xs, xt⟩⟩

example : s ∩ t = t ∩ s := by ext x; simp [and_comm]

example : s ∩ t = t ∩ s := by
  apply Subset.antisymm
  · rintro x ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro x ⟨xt, xs⟩; exact ⟨xs, xt⟩

example : s ∩ t = t ∩ s :=
    Subset.antisymm (fun _ ⟨xs, xt⟩ ↦ ⟨xt, xs⟩) fun _ ⟨xt, xs⟩ ↦ ⟨xs, xt⟩

example : s ∩ (s ∪ t) = s := by
  ext x
  constructor
  intro h1
  apply h1.1
  intro h1
  simp only [subset_def, mem_inter_iff] at *
  constructor
  apply h1
  apply mem_union_left
  apply h1




example : s ∪ s ∩ t = s := by
  ext x
  constructor
  intro h1
  rcases h1 with h2 | h2
  apply h2
  apply h2.1
  intro h1
  apply mem_union_left
  apply h1



example : s \ t ∪ t = s ∪ t := by
  ext x
  constructor
  intro h
  rcases h with h1 | h1
  obtain ⟨h2, _⟩ := h1
  apply mem_union_left
  apply h2
  apply mem_union_right
  apply h1
  intro h
  by_cases h1 : x ∈ s \ t
  constructor
  apply h1
  push_neg at h1
  by_cases h2 : x ∈ t
  apply mem_union_right
  apply h2
  by_cases h3 : x ∈ s
  have h4 : x ∈ s \ t := by
    exact mem_diff_of_mem h3 h2
  contradiction
  have h4 : x ∉ s ∪ t := by
    intro h5
    rcases h5 with h | h
    contradiction
    contradiction
  contradiction


example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  ext x
  constructor
  intro h1
  rcases h1 with h2 | h2
  have qq : x ∈ s ∧ x ∉ t := by exact h2
  obtain ⟨h3, h4⟩ := qq
  constructor
  apply mem_union_left
  apply h3
  intro h5
  obtain ⟨_, h7⟩ := h5
  contradiction
  have qq : x ∈ t ∧ x ∉ s := by exact h2
  obtain ⟨h3, h4⟩ := qq
  constructor
  apply mem_union_right
  apply h3
  intro h5
  obtain ⟨h6, _⟩ := h5
  contradiction
  intro h1
  have qq : x ∈ (s ∪ t) ∧ x ∉ (s ∩ t) := by exact h1
  obtain ⟨h3, h4⟩ := qq
  by_cases h5 : x ∈ s
  by_cases h6 : x ∈ t
  have cc : x ∈ (s ∩ t) := mem_inter h5 h6
  contradiction
  have h7: x ∈ s \ t := mem_diff_of_mem h5 h6
  apply mem_union_left
  apply h7
  by_cases h6 : x ∈ t
  have h7: x ∈ t \ s := mem_diff_of_mem h6 h5
  apply mem_union_right
  apply h7
  have h7 : x ∈ s ∨ x ∈ t := h3
  obtain h8 | h8 := h7
  contradiction
  contradiction

def evens : Set ℕ :=
  { n | Even n }

def odds : Set ℕ :=
  { n | ¬Even n }

example : evens ∪ odds = univ := by
  rw [evens, odds]
  ext n
  simp [-Nat.not_even_iff_odd]
  apply Classical.em

example (x : ℕ) (h : x ∈ (∅ : Set ℕ)) : False :=
  h

example (x : ℕ) : x ∈ (univ : Set ℕ) :=
  trivial

example : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
  intro n
  intro h
  obtain ⟨h1, h2⟩ := h
  have h3 : n > 2 := h2
  have h4 : Nat.Prime n := h1
  have h5 := Nat.Prime.eq_two_or_odd h4
  rcases h5 with h6 | h7
  rw [h6] at h3
  contradiction
  dsimp
  exact Nat.not_even_iff.mpr h7





#print Prime

#print Nat.Prime

example (n : ℕ) : Prime n ↔ Nat.Prime n :=
  Nat.prime_iff.symm

example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rw [Nat.prime_iff]
  exact h

example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rwa [Nat.prime_iff]

end

section

variable (s t : Set ℕ)

example (h₀ : ∀ x ∈ s, ¬Even x) (h₁ : ∀ x ∈ s, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  intro x xs
  constructor
  · apply h₀ x xs
  apply h₁ x xs

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ s, Prime x := by
  rcases h with ⟨x, xs, _, prime_x⟩
  use x, xs

section
variable (ssubt : s ⊆ t)

example (h₀ : ∀ x ∈ t, ¬Even x) (h₁ : ∀ x ∈ t, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  sorry

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ t, Prime x := by
  sorry

end

end

section
variable {α I : Type*}
variable (A B : I → Set α)
variable (s : Set α)

open Set

example : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s := by
  ext x
  simp only [mem_inter_iff, mem_iUnion]
  constructor
  · rintro ⟨xs, ⟨i, xAi⟩⟩
    exact ⟨i, xAi, xs⟩
  rintro ⟨i, xAi, xs⟩
  exact ⟨xs, ⟨i, xAi⟩⟩

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  ext x
  simp only [mem_inter_iff, mem_iInter]
  constructor
  · intro h
    constructor
    · intro i
      exact (h i).1
    intro i
    exact (h i).2
  rintro ⟨h1, h2⟩ i
  constructor
  · exact h1 i
  exact h2 i


example : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  sorry

def primes : Set ℕ :=
  { x | Nat.Prime x }

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } :=by
  ext
  rw [mem_iUnion₂]
  simp

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } := by
  ext
  simp

example : (⋂ p ∈ primes, { x | ¬p ∣ x }) ⊆ { x | x = 1 } := by
  intro x
  contrapose!
  simp
  apply Nat.exists_prime_and_dvd

example : (⋃ p ∈ primes, { x | x ≤ p }) = univ := by
  sorry

end

section

open Set

variable {α : Type*} (s : Set (Set α))

example : ⋃₀ s = ⋃ t ∈ s, t := by
  ext x
  rw [mem_iUnion₂]
  simp

example : ⋂₀ s = ⋂ t ∈ s, t := by
  ext x
  rw [mem_iInter₂]
  rfl

end
