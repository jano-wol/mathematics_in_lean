import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S03

section
variable (a b : ℝ)

example (h : a < b) : ¬b < a := by
  intro h'
  have : a < a := lt_trans h h'
  apply lt_irrefl a this

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a

variable (f : ℝ → ℝ)

example (h : ∀ a, ∃ x, f x > a) : ¬FnHasUb f := by
  intro fnub
  rcases fnub with ⟨a, fnuba⟩
  rcases h a with ⟨x, hx⟩
  have : f x ≤ a := fnuba x
  linarith

example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f := by
  intro n
  obtain ⟨r, hr⟩ := n
  dsimp [FnLb] at hr
  have h3 := h r
  obtain ⟨s, hs⟩ := h3
  have h4 := hr s
  linarith




example : ¬FnHasUb fun x ↦ x := by
  intro n
  dsimp [FnHasUb] at *
  dsimp [FnUb] at *
  obtain ⟨r, ha⟩ := n
  have hc := ha (r + 1)
  linarith


#check (not_le_of_gt : a > b → ¬a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬a < b)
#check (lt_of_not_ge : ¬a ≥ b → a < b)
#check (le_of_not_gt : ¬a > b → a ≤ b)

example (h : Monotone f) (h' : f a < f b) : a < b := by
  dsimp [Monotone] at h
  apply lt_of_not_ge
  intro n
  have h2 := h n
  linarith

example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  intro n
  have h2 := n h
  linarith

example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  let f := fun _ : ℝ ↦ (0 : ℝ)
  have monof : Monotone f := by
    dsimp [Monotone]
    intro p q _
    linarith
  have h' : f 1 ≤ f 0 := le_refl _
  have h2 : ∀ {a b : ℝ}, f a ≤ f b → a ≤ b := h monof
  have h3 : (1 : ℝ)  ≤ 0 := h2 h'
  linarith

example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  apply le_of_not_gt
  intro n
  have h1 : 0 < (x / 2) := by linarith[n]
  have h2 := h (x / 2) h1
  linarith
end

section
variable {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  intro x
  intro n
  have h2 : ∃ x, P x := by
    use x
  contradiction

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  intro n
  obtain ⟨x, hx⟩ := n
  have h2 := h x
  contradiction

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  show P x
  by_contra h''
  exact h' ⟨x, h''⟩

example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  intro n
  obtain ⟨x, hx⟩ := h
  have h2 := n x
  contradiction

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  show P x
  by_contra h''
  exact h' ⟨x, h''⟩

example (h : ¬¬Q) : Q := by
  by_contra h'
  contradiction

example (h : Q) : ¬¬Q := by
  intro n
  contradiction

end

section
variable (f : ℝ → ℝ)

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  have h2 : ∀ a, ¬∀ (x : ℝ), f x ≤ a := by
    intro x
    intro n
    have h2 : ∃ a, ∀ (x : ℝ), f x ≤ a := by
      use x
    contradiction
  have h3 : ∀ a, ∃ (x : ℝ), ¬f x ≤ a := by
    intro a
    have  h3 := h2 a
    by_contra h'
    apply h3
    intro x
    by_contra h''
    exact h' ⟨x, h''⟩
  intro a
  obtain ⟨x, hx⟩ := h3 a
  use x
  exact not_le.mp hx


example (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  dsimp only [FnHasUb, FnUb] at h
  push_neg at h
  exact h

example (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
  dsimp [Monotone] at h
  push_neg at h
  obtain ⟨a, b, hab⟩ := h
  obtain ⟨hab1, hab2⟩ := hab
  use a, b


example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  contrapose! h
  exact h

example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  contrapose! h
  use x / 2
  constructor <;> linarith

end

section
variable (a : ℕ)

example (h : 0 < 0) : a > 37 := by
  exfalso
  apply lt_irrefl 0 h

example (h : 0 < 0) : a > 37 :=
  absurd h (lt_irrefl 0)

example (h : 0 < 0) : a > 37 := by
  have _' : ¬0 < 0 := lt_irrefl 0
  contradiction

end
