import MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext x
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x
    constructor
    apply Or.inl
    apply xs
    rfl
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  intro h1
  intro x
  intro xs
  have h2 : f x ∈ f '' s := mem_image_of_mem f xs
  apply h1 h2
  intro h1
  intro x
  intro xs
  rcases xs with ⟨y, ys, fyeq⟩
  rw [← fyeq]
  apply h1 ys




example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  dsimp [Injective] at *
  intro x xs
  rcases xs with ⟨t, ts, fte⟩
  have h2 := h fte
  rw [← h2]
  apply ts


example : f '' (f ⁻¹' u) ⊆ u := by
  intro x hx
  rcases hx with ⟨r, rs, rte⟩
  have h2 : f r ∈ u := rs
  rw [← rte]
  apply h2


example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  intro x hx
  dsimp [Surjective] at *
  have h1 := h x
  obtain ⟨r, ht⟩ := h1
  use r
  constructor
  simp
  rw [ht]
  apply hx
  apply ht


example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  intro r hr
  simp
  simp at hr
  obtain ⟨q, hq⟩ := hr
  obtain ⟨hq1, hq2⟩ := hq
  use q
  constructor
  apply h hq1
  apply hq2

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  intro r hr
  simp at *
  apply h hr

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext x
  constructor
  intro hr
  simp at *
  apply hr
  intro hr
  simp at *
  apply hr


example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  intro r hr
  simp at *
  obtain ⟨q , ⟨⟨hq3, hq4⟩ , hq2⟩⟩ := hr
  constructor
  use q
  use q


example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  intro r hr
  dsimp [Injective] at h
  simp at *
  obtain ⟨⟨r3, ⟨hq5, hq6⟩⟩ , ⟨r2, ⟨hq3, hq4⟩⟩⟩ := hr
  use r2
  constructor
  constructor
  rw [← hq6] at hq4
  have h1 := h hq4
  rw [h1]
  apply hq5
  apply hq3
  apply hq4



example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  intro r hr
  simp at *
  obtain ⟨⟨r3, ⟨hq5, hq6⟩⟩ , r2⟩ := hr
  use r3
  constructor
  constructor
  apply hq5
  intro cc
  have h2 := r2 r3 cc
  contradiction
  apply hq6


example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  intro r hr
  simp at *
  apply hr

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext r
  simp at *
  constructor
  intro hx
  obtain ⟨⟨r3, ⟨hq5, hq6⟩⟩, r2⟩ := hx
  use r3
  constructor
  constructor
  apply hq5
  rw [hq6]
  apply r2
  apply hq6
  intro hx
  obtain ⟨h, ⟨⟨t3, t4⟩ , t2⟩ ⟩ := hx
  constructor
  use h
  rw [← t2]
  apply t4



example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  intro r hr
  simp at *
  obtain ⟨h, ⟨⟨t3, t4⟩ , t2⟩ ⟩ := hr
  constructor
  use h
  rw [← t2]
  apply t4


example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  intro r hr
  simp at *
  obtain ⟨h, t2⟩ := hr
  constructor
  use r
  apply t2

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  intro r hr
  simp at *
  obtain h | h := hr
  left
  use r
  right
  apply h

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext r
  simp at *
  constructor
  intro h
  obtain ⟨t1, ⟨⟨i, hj⟩ , hi⟩ ⟩ := h
  use i
  use t1
  intro h
  obtain ⟨t1, ⟨i, ⟨j, k⟩⟩ ⟩ := h
  use i
  constructor
  use t1
  apply k


example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  intro r hr
  simp at *
  obtain ⟨t1, ⟨i, ⟨j, k⟩⟩ ⟩ := hr
  intro j
  have h := i j
  use t1


example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  intro r hr
  simp at *
  dsimp [Injective] at *
  have h2 := hr i
  obtain ⟨t1, ⟨_, j⟩ ⟩ := h2
  have hr_all: ∀ (i : I), t1 ∈ A i := by
    intro jj
    have hj := hr jj
    obtain ⟨qq, ⟨rr1, rr2⟩⟩ := hj
    rw [← j] at rr2
    have h3 := injf rr2
    rw [← h3]
    apply rr1
  use t1



example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  ext r
  simp at *


example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext r
  simp at *

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  sorry

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  sorry

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  sorry

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  sorry

end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f :=
  sorry

example : Surjective f ↔ RightInverse (inverse f) f :=
  sorry

end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S
  sorry
  have h₃ : j ∉ S
  sorry
  contradiction

-- COMMENTS: TODO: improve this
end
