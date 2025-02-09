import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Charpoly.Basic

import MIL.Common




variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

variable {W : Type*} [AddCommGroup W] [Module K W]


open Polynomial Module LinearMap

example (φ ψ : End K V) : φ * ψ = φ ∘ₗ ψ :=
  LinearMap.mul_eq_comp φ ψ -- `rfl` would also work

-- evaluating `P` on `φ`
example (P : K[X]) (φ : End K V) : V →ₗ[K] V :=
  aeval φ P

-- evaluating `X` on `φ` gives back `φ`
example (φ : End K V) : aeval φ (X : K[X]) = φ :=
  aeval_X φ



#check Submodule.eq_bot_iff
#check Submodule.mem_inf
#check LinearMap.mem_ker


lemma l1 (p1 p2 : K[X]) (φ : End K V) : (aeval φ) (p1 * p2) = ((aeval φ) p1) * ((aeval φ) p2) := by exact aeval_mul φ
lemma l2 (p1 p2 : K[X]) (v : V) (φ : End K V) : ((aeval φ) (p1 * p2)) v = (((aeval φ) p1) * ((aeval φ) p2)) v := by
  rw[l1]
lemma l3 (φ η : End K V) (v : V) : (φ * η) v = φ (η v) := by exact rfl
lemma l4 (p1 p2 : K[X]) (v : V) (φ : End K V) : ((aeval φ) (p1 * p2)) v = ((aeval φ) p1)  (((aeval φ) p2) v) := by
  rw [l2]
  rw [l3]



example (P Q : K[X]) (h : IsCoprime P Q) (φ : End K V) : ker (aeval φ P) ⊓ ker (aeval φ Q) = ⊥ := by
  ext v
  constructor
  intro h1
  obtain⟨h2, ⟨h3, h4⟩⟩ := h
  have h5 : v ∈ ker ((aeval φ) P) := (Submodule.mem_inf.mp h1).1
  have h6 : v ∈ ker ((aeval φ) Q) := (Submodule.mem_inf.mp h1).2
  have h7 : (aeval φ) P v = 0 := by apply h5
  have h8 : (aeval φ) Q v = 0 := by apply h6
  have h9 : (aeval φ) (h2 * P) v  = 0 := by
    rw [l4]
    rw [h7]
    exact LinearMap.map_zero ((aeval φ) h2)
  have h10 : (aeval φ) (h3 * Q) v  = 0 := by
    rw [l4]
    rw [h8]
    exact LinearMap.map_zero ((aeval φ) h3)
  have h11 : (aeval φ) (h2 * P + h3 * Q) v = (aeval φ) (h2 * P) v + (aeval φ) (h3 * Q) v := by simp
  have h12 : ((aeval φ) (1 : K[X])) v = 0 := by
    rw [← h4]
    rw [h11]
    rw [h9, h10]
    simp
  simp
  simp at h12
  apply h12
  intro h1
  exact
    (Submodule.Quotient.mk_eq_zero (ker ((aeval φ) P) ⊓ ker ((aeval φ) Q))).mp
      (congrArg Submodule.Quotient.mk h1)


#check Submodule.add_mem_sup
#check map_mul
#check LinearMap.mul_apply
#check LinearMap.ker_le_ker_comp

example (P Q : K[X]) (h : IsCoprime P Q) (φ : End K V) :
    ker (aeval φ P) ⊔ ker (aeval φ Q) = ker (aeval φ (P*Q)) := by
  apply le_antisymm
  · apply sup_le
    · rw [mul_comm, map_mul]
      apply ker_le_ker_comp -- or alternative below:
      -- intro x hx
      -- rw [mul_comm, mem_ker] at *
      -- simp [hx]
    · rw [map_mul]
      apply ker_le_ker_comp -- or alternative as above
  · intro x hx
    rcases h with ⟨U, V, hUV⟩
    have key : x = aeval φ (U*P) x + aeval φ (V*Q) x := by simpa using congr((aeval φ) $hUV.symm x)
    rw [key, add_comm]
    apply Submodule.add_mem_sup <;> rw [mem_ker] at *
    · rw [← mul_apply, ← map_mul, show P*(V*Q) = V*(P*Q) by ring, map_mul, mul_apply, hx,
          map_zero]
    · rw [← mul_apply, ← map_mul, show Q*(U*P) = U*(P*Q) by ring, map_mul, mul_apply, hx,
          map_zero]

example (a : K) : algebraMap K (End K V) a = a • LinearMap.id := rfl

example (φ : End K V) (a : K) :
    φ.eigenspace a = LinearMap.ker (φ - algebraMap K (End K V) a) :=
  rfl



example (φ : End K V) (a : K) : φ.HasEigenvalue a ↔ φ.eigenspace a ≠ ⊥ :=
  Iff.rfl

example (φ : End K V) (a : K) : φ.HasEigenvalue a ↔ ∃ v, φ.HasEigenvector a v  :=
  ⟨End.HasEigenvalue.exists_hasEigenvector, fun ⟨_, hv⟩ ↦ φ.hasEigenvalue_of_hasEigenvector hv⟩

example (φ : End K V) : φ.Eigenvalues = {a // φ.HasEigenvalue a} :=
  rfl

-- Eigenvalue are roots of the minimal polynomial
example (φ : End K V) (a : K) : φ.HasEigenvalue a → (minpoly K φ).IsRoot a :=
  φ.isRoot_of_hasEigenvalue

-- In finite dimension, the converse is also true (we will discuss dimension below)
example [FiniteDimensional K V] (φ : End K V) (a : K) :
    φ.HasEigenvalue a ↔ (minpoly K φ).IsRoot a :=
  φ.hasEigenvalue_iff_isRoot

-- Cayley-Hamilton
example [FiniteDimensional K V] (φ : End K V) : aeval φ φ.charpoly = 0 :=
  φ.aeval_self_charpoly
