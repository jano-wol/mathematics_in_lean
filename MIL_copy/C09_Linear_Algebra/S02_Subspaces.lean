import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Charpoly.Basic

import MIL.Common


variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

example (U : Submodule K V) {x y : V} (hx : x ∈ U) (hy : y ∈ U) :
    x + y ∈ U :=
  U.add_mem hx hy

example (U : Submodule K V) {x : V} (hx : x ∈ U) (a : K) :
    a • x ∈ U :=
  U.smul_mem a hx


noncomputable example : Submodule ℝ ℂ where
  carrier := Set.range ((↑) : ℝ → ℂ)
  add_mem' := by
    rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
    use n + m
    simp
  zero_mem' := by
    use 0
    simp
  smul_mem' := by
    rintro c - ⟨a, rfl⟩
    use c*a
    simp


def preimage {W : Type*} [AddCommGroup W] [Module K W] (φ : V →ₗ[K] W) (H : Submodule K W) :
    Submodule K V where
  carrier := φ ⁻¹' H
  zero_mem' := by
    dsimp
    rw [Set.mem_preimage]
    simp
  add_mem' := by
    intro v1 v2 h1 h2
    rw [Set.mem_preimage] at *
    have h : φ (v1 + v2) = φ (v1) + φ (v2) := by exact LinearMap.map_add φ v1 v2
    rw [h]
    exact add_mem h1 h2
  smul_mem' := by
    dsimp
    intro c v h
    rw [Set.mem_preimage] at *
    rw [LinearMap.map_smul φ]
    have j := H.smul_mem c h
    simp
    apply j


example (U : Submodule K V) : Module K U := inferInstance

example (U : Submodule K V) : Module K {x : V // x ∈ U} := inferInstance

example (H H' : Submodule K V) :
    ((H ⊓ H' : Submodule K V) : Set V) = (H : Set V) ∩ (H' : Set V) := rfl

example (H H' : Submodule K V) :
    ((H ⊔ H' : Submodule K V) : Set V) = Submodule.span K ((H : Set V) ∪ (H' : Set V)) := by
  simp [Submodule.span_union]

example (x : V) : x ∈ (⊤ : Submodule K V) := trivial

example (x : V) : x ∈ (⊥ : Submodule K V) ↔ x = 0 := Submodule.mem_bot K


-- If two subspaces are in direct sum then they span the whole space.
example (U V : Submodule K V) (h : IsCompl U V) :
  U ⊔ V = ⊤ := h.sup_eq_top

-- If two subspaces are in direct sum then they intersect only at zero.
example (U V : Submodule K V) (h : IsCompl U V) :
  U ⊓ V = ⊥ := h.inf_eq_bot

section
open DirectSum
variable {ι : Type*} [DecidableEq ι]

-- If subspaces are in direct sum then they span the whole space.
example (U : ι → Submodule K V) (h : DirectSum.IsInternal U) :
  ⨆ i, U i = ⊤ := h.submodule_iSup_eq_top

-- If subspaces are in direct sum then they pairwise intersect only at zero.
example {ι : Type*} [DecidableEq ι] (U : ι → Submodule K V) (h : DirectSum.IsInternal U)
    {i j : ι} (hij : i ≠ j) : U i ⊓ U j = ⊥ :=
  (h.submodule_independent.pairwiseDisjoint hij).eq_bot

-- Those conditions characterize direct sums.
#check DirectSum.isInternal_submodule_iff_independent_and_iSup_eq_top

-- The relation with external direct sums: if a family of subspaces is
-- in internal direct sum then the map from their external direct sum into `V`
-- is a linear isomorphism.
noncomputable example {ι : Type*} [DecidableEq ι] (U : ι → Submodule K V)
    (h : DirectSum.IsInternal U) : (⨁ i, U i) ≃ₗ[K] V :=
  LinearEquiv.ofBijective (coeLinearMap U) h
end

example {s : Set V} (E : Submodule K V) : Submodule.span K s ≤ E ↔ s ⊆ E :=
  Submodule.span_le

example : GaloisInsertion (Submodule.span K) ((↑) : Submodule K V → Set V) :=
  Submodule.gi K V

example {S T : Submodule K V} {x : V} (h : x ∈ S ⊔ T) :
    ∃ s ∈ S, ∃ t ∈ T, x = s + t  := by
  rw [← S.span_eq, ← T.span_eq, ← Submodule.span_union] at h
  apply Submodule.span_induction h (p := fun x ↦ ∃ s ∈ S, ∃ t ∈ T, x = s + t)
  · rintro x (hx|hx)
    · use x, hx, 0, T.zero_mem
      module
    · use 0, S.zero_mem, x, hx
      module
  · use 0, S.zero_mem, 0, T.zero_mem
    module
  · rintro - - ⟨s, hs, t, ht, rfl⟩ ⟨s', hs', t', ht', rfl⟩
    use s + s', S.add_mem hs hs', t + t', T.add_mem ht ht'
    module
  · rintro a - ⟨s, hs, t, ht, rfl⟩
    use a • s, S.smul_mem a hs, a • t, T.smul_mem a ht
    module


section

variable {W : Type*} [AddCommGroup W] [Module K W] (φ : V →ₗ[K] W)

variable (E : Submodule K V) in
#check (Submodule.map φ E : Submodule K W)

variable (F : Submodule K W) in
#check (Submodule.comap φ F : Submodule K V)

example : LinearMap.range φ = .map φ ⊤ := LinearMap.range_eq_map φ

example : LinearMap.ker φ = .comap φ ⊥ := Submodule.comap_bot φ -- or `rfl`



open Function LinearMap

example : Injective φ ↔ ker φ = ⊥ := ker_eq_bot.symm

example : Surjective φ ↔ range φ = ⊤ := range_eq_top.symm

#check Submodule.mem_map_of_mem
#check Submodule.mem_map --  x ∈ map f p ↔ ∃ y, y ∈ p ∧ f y = x
#check Submodule.mem_comap -- x ∈ comap f p ↔ f x ∈ p

example (E : Submodule K V) (F : Submodule K W) :
    Submodule.map φ E ≤ F ↔ E ≤ Submodule.comap φ F := by
  constructor
  intro h
  intro e he
  simp
  have key : φ e ∈ Submodule.map φ E := by exact Submodule.mem_map_of_mem he
  exact h key
  intro h
  intro x hx
  have key : ∃ y, y ∈ E ∧ φ y = x := Submodule.mem_map.2 hx
  obtain ⟨t, ⟨ht, htt⟩⟩ := key
  have key2 : t ∈ Submodule.comap φ F := by exact h ht
  have key3 := Submodule.mem_comap.1 key2
  rw [htt] at key3
  apply key3



variable (E : Submodule K V)

example : Module K (V ⧸ E) := inferInstance

example : V →ₗ[K] V ⧸ E := E.mkQ

example : ker E.mkQ = E := E.ker_mkQ

example : range E.mkQ = ⊤ := E.range_mkQ

example (hφ : E ≤ ker φ) : V ⧸ E →ₗ[K] W := E.liftQ φ hφ

example (F : Submodule K W) (hφ : E ≤ .comap φ F) : V ⧸ E →ₗ[K] W ⧸ F := E.mapQ F φ hφ

noncomputable example : (V ⧸ LinearMap.ker φ) ≃ₗ[K] range φ := φ.quotKerEquivRange


open Submodule

#check Submodule.map_comap_eq -- (f : F) (q : Submodule R₂ M₂) : map f (comap f q) = range f ⊓ q
#check Submodule.comap_map_eq -- (f : F) (p : Submodule R M) : comap f (map f p) = p ⊔ LinearMap.ker f

example : Submodule K (V ⧸ E) ≃ { F : Submodule K V // E ≤ F } where
  toFun F :=
    let P := Submodule.comap E.mkQ F;
    have hP : E ≤ P := by
      -- Show that the comap of `F` is contained in `E` using the kernel.
      rw [← E.ker_mkQ, ← Submodule.comap_bot]
      apply Submodule.comap_mono
      exact bot_le
    ⟨P, hP⟩
  invFun P := map E.mkQ P
  left_inv P := by
    dsimp
    rw [Submodule.map_comap_eq, E.range_mkQ]
    exact top_inf_eq P
  right_inv := by
    intro P
    ext x
    dsimp only
    rw [Submodule.comap_map_eq, E.ker_mkQ, sup_of_le_left]
    exact P.2
