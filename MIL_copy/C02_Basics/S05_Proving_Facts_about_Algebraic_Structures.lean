import MIL.Common
import Mathlib.Topology.MetricSpace.Basic

section
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)


#check x < y
#check (lt_irrefl x : ¬ (x < x))
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne

end

section
variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  apply le_inf
  apply inf_le_right
  apply inf_le_left
  apply le_inf
  apply inf_le_right
  apply inf_le_left


example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  apply le_inf
  calc
    x ⊓ y ⊓ z ≤ x ⊓ y := by apply inf_le_left
    _ ≤ x := by apply inf_le_left
  apply le_inf
  calc
    x ⊓ y ⊓ z ≤ x ⊓ y := by apply inf_le_left
    _ ≤ y := by apply inf_le_right
  apply inf_le_right
  apply le_inf
  apply le_inf
  apply inf_le_left
  calc
    x ⊓ (y ⊓ z) ≤ y ⊓ z := by apply inf_le_right
    _ ≤ y := by apply inf_le_left
  calc
    x ⊓ (y ⊓ z) ≤ y ⊓ z := by apply inf_le_right
    _ ≤ z := by apply inf_le_right



example : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  apply sup_le
  apply le_sup_right
  apply le_sup_left
  apply sup_le
  apply le_sup_right
  apply le_sup_left

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply le_antisymm
  apply sup_le
  apply sup_le
  apply le_sup_left
  calc
    y ≤ y ⊔ z := by apply le_sup_left
    _ ≤ x ⊔ (y ⊔ z) := by apply le_sup_right
  calc
    z ≤ y ⊔ z := by apply le_sup_right
    _ ≤ x ⊔ (y ⊔ z) := by apply le_sup_right
  apply sup_le
  calc
    x ≤ x ⊔ y := by apply le_sup_left
    _ ≤ x ⊔ y ⊔ z := by apply le_sup_left
  apply sup_le
  calc
    y ≤ x ⊔ y := by apply le_sup_right
    _ ≤ x ⊔ y ⊔ z := by apply le_sup_left
  apply le_sup_right


theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  apply inf_le_left
  apply le_inf
  apply le_refl
  apply le_sup_left



theorem absorb2 : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  apply sup_le
  apply le_refl
  apply inf_le_left
  apply le_sup_left


end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right x y z : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right x y z : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  apply le_antisymm
  apply sup_le
  apply le_inf
  apply le_sup_left
  apply le_sup_left
  apply le_inf
  calc
    b ⊓ c ≤ b := by apply inf_le_left
    _ ≤ a ⊔ b := by apply le_sup_right
  calc
    b ⊓ c ≤ c := by apply inf_le_right
    _ ≤ a ⊔ c := by apply le_sup_right
  have h2 := h (a ⊔ b) a c
  rw [h2]
  apply sup_le
  have h3 : (a ⊔ b) ⊓ a = a ⊓ (a ⊔ b) := by rw [inf_comm]
  rw [h3]
  rw [absorb1]
  apply le_sup_left
  rw [inf_comm]
  rw [h]
  apply sup_le
  calc
    c ⊓ a ≤ a := by apply inf_le_right
    _ ≤ a ⊔ b ⊓ c := by apply le_sup_left
  rw [inf_comm]
  apply le_sup_right





example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  apply le_antisymm
  rw [h]
  apply le_inf
  rw [sup_comm (a ⊓ b)]
  rw [absorb2]
  apply inf_le_left
  rw [sup_comm (a ⊓ b)]
  rw [h]
  apply le_inf
  calc
    a ⊓ (b ⊔ c) ≤ a := by apply inf_le_left
    _ ≤ c ⊔ a := by apply le_sup_right
  rw [sup_comm]
  apply inf_le_right
  apply sup_le
  apply le_inf
  apply inf_le_left
  calc
    a ⊓ b ≤ b := by apply inf_le_right
    _ ≤ b ⊔ c := by apply le_sup_left
  apply le_inf
  apply inf_le_left
  calc
    a ⊓ c ≤ c := by apply inf_le_right
    _ ≤ b ⊔ c := by apply le_sup_right

end

section
variable {R : Type*} [StrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

theorem help1 (h : a ≤ b) : 0 ≤ b - a := by
  have h2 :  ∀ c, c + a ≤ c + b := by apply add_le_add_left h
  have h3 := h2 (-a)
  rw [neg_add_cancel] at h3
  have h4 : -a + b = b - a := by
    rw [add_comm]
    rw [sub_eq_add_neg]
  rw [← h4]
  apply h3

theorem help2 (h: 0 ≤ b - a) : a ≤ b := by
  have h2 :  ∀ c, c + 0 ≤ c + (b - a) := by apply add_le_add_left h
  have h3 := h2 a
  rw [add_zero] at h3
  have h4 : a + (b - a) = b := by
    rw [add_comm]
    exact sub_add_cancel b a
  rw [h4] at h3
  apply h3

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  have h2 := help1 _ _ h
  have h3 := mul_nonneg h2 h'
  rw [sub_mul] at h3
  have h4 := help2 _ _ h3
  apply h4

end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

example (x y : X) : 0 ≤ dist x y := by
  have h := dist_triangle x y x
  calc
    (0 : ℝ)  = 0 / 2  := by ring
    _ = (dist x x) / 2 := by rw [dist_self]
    _ ≤ (dist x y + dist y x) / 2 := by linarith[h]
    _ = (dist x y + dist x y) / 2 := by rw [dist_comm]
    _ = dist x y := by ring
end
