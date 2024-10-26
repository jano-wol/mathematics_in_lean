import Mathlib.Data.Nat.Prime.Basic
import MIL.Common

open BigOperators

namespace C05S03

theorem two_le {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  cases m; contradiction
  case succ m =>
    cases m; contradiction
    repeat apply Nat.succ_le_succ
    apply zero_le

example {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  by_contra h
  push_neg at h
  interval_cases m
  contradiction
  contradiction

example {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  by_contra h
  push_neg at h
  revert h0 h1
  revert h m
  decide

theorem exists_prime_factor {n : Nat} (h : 2 ≤ n) : ∃ p : Nat, p.Prime ∧ p ∣ n := by
  by_cases np : n.Prime
  · use n, np
  induction' n using Nat.strong_induction_on with n ih
  rw [Nat.prime_def_lt] at np
  push_neg at np
  rcases np h with ⟨m, mltn, mdvdn, mne1⟩
  have : m ≠ 0 := by
    intro mz
    rw [mz, zero_dvd_iff] at mdvdn
    linarith
  have mgt2 : 2 ≤ m := two_le this mne1
  by_cases mp : m.Prime
  · use m, mp
  · rcases ih m mltn mgt2 mp with ⟨p, pp, pdvd⟩
    use p, pp
    apply pdvd.trans mdvdn


theorem primes_infinite : ∀ n, ∃ p > n, Nat.Prime p := by
  intro n
  have : 2 ≤ Nat.factorial (n + 1) + 1 := by
    have r: 1 ≤ Nat.factorial (n + 1) := by
      rw [Nat.factorial]
      have r1 : 1 ≤ n.succ := by exact NeZero.one_le
      have r2 : 1 ≤ n.factorial := by
        induction' n with n ih
        rw [Nat.factorial]
        have h : 1 ≤ n.succ := by exact NeZero.one_le
        have h2 := ih h
        rw [Nat.factorial]
        calc
          n.succ * n.factorial ≥ 1 * n.factorial := by rel [h]
          _ ≥ 1 * 1 := by rel [h2]
          _ = 1 := by ring
      calc
        n.succ * n.factorial ≥ 1 * n.factorial := by rel [r1]
        _ ≥ 1 * 1 := by rel [r2]
        _ = 1 := by ring
    calc
      (n + 1).factorial + 1 ≥ 1 + 1 := by rel [r]
      _ = 2 := by ring
  rcases exists_prime_factor this with ⟨p, pp, pdvd⟩
  refine ⟨p, ?_, pp⟩
  show p > n
  by_contra ple
  push_neg  at ple
  have : p ∣ Nat.factorial (n + 1) := by
    refine Nat.dvd_factorial ?_ ?_
    exact Nat.Prime.pos pp
    linarith
  have : p ∣ 1 := by
    exact (Nat.dvd_add_iff_right this).mpr pdvd
  show False
  have hhh : p ≤ 1 := by exact (Nat.Prime.dvd_factorial pp).mp this
  have hhhh : 2 ≤ p := by exact Nat.Prime.two_le pp
  linarith
open Finset

section
variable {α : Type*} [DecidableEq α] (r s t : Finset α)

example : r ∩ (s ∪ t) ⊆ r ∩ s ∪ r ∩ t := by
  rw [subset_iff]
  intro x
  rw [mem_inter, mem_union, mem_union, mem_inter, mem_inter]
  tauto

example : r ∩ (s ∪ t) ⊆ r ∩ s ∪ r ∩ t := by
  simp [subset_iff]
  intro x
  tauto

example : r ∩ s ∪ r ∩ t ⊆ r ∩ (s ∪ t) := by
  simp [subset_iff]
  intro x
  tauto

example : r ∩ s ∪ r ∩ t = r ∩ (s ∪ t) := by
  ext x
  simp
  tauto

end

section
variable {α : Type*} [DecidableEq α] (r s t : Finset α)

example : (r ∪ s) ∩ (r ∪ t) = r ∪ s ∩ t := by
  ext x
  simp
  tauto

example : (r \ s) \ t = r \ (s ∪ t) := by
  ext x
  simp
  tauto

end

example (s : Finset ℕ) (n : ℕ) (h : n ∈ s) : n ∣ ∏ i in s, i :=
  Finset.dvd_prod_of_mem _ h

theorem _root_.Nat.Prime.eq_of_dvd_of_prime {p q : ℕ}
      (prime_p : Nat.Prime p) (prime_q : Nat.Prime q) (h : p ∣ q) :
    p = q := by
  have h1 := (Nat.Prime.eq_one_or_self_of_dvd prime_q) p h
  obtain h1 | h1 := h1
  have h2 : p ≠ 1 := by exact Nat.Prime.ne_one prime_p
  contradiction
  apply h1


theorem mem_of_dvd_prod_primes {s : Finset ℕ} {p : ℕ} (prime_p : p.Prime) :
    (∀ n ∈ s, Nat.Prime n) → (p ∣ ∏ n in s, n) → p ∈ s := by
  intro h₀ h₁
  induction' s using Finset.induction_on with a s ans ih
  · simp at h₁
    linarith [prime_p.two_le]
  simp [Finset.prod_insert ans, prime_p.dvd_mul] at h₀ h₁
  rw [mem_insert]
  rcases h₀ with ⟨vv, ww⟩
  have ww2 := ih ww
  obtain vv1 | vv1 := h₁
  have rrr := _root_.Nat.Prime.eq_of_dvd_of_prime prime_p vv vv1
  left
  apply rrr
  have rrr := ww2 vv1
  right
  apply rrr

example (s : Finset ℕ) (x : ℕ) : x ∈ s.filter Nat.Prime ↔ x ∈ s ∧ x.Prime :=
  mem_filter

theorem primes_infinite' : ∀ s : Finset Nat, ∃ p, Nat.Prime p ∧ p ∉ s := by
  intro s
  by_contra h
  push_neg at h
  set s' := s.filter Nat.Prime with s'_def
  have mem_s' : ∀ {n : ℕ}, n ∈ s' ↔ n.Prime := by
    intro n
    simp [s'_def]
    apply h
  have : 2 ≤ (∏ i in s', i) + 1 := by
    have aux : (∏ i in s', i) > 0 := by
      apply Finset.prod_pos
      intro i
      intro is
      have q := mem_s'.mp is
      exact Nat.Prime.pos q
    have aux2 : (∏ i in s', i) ≥ 1 := by
      linarith[aux]
    calc
      (∏ i in s', i) + 1 ≥ 1 + 1 := by rel [aux2]
      _ = 2 := by ring
  rcases exists_prime_factor this with ⟨p, pp, pdvd⟩
  have : p ∣ ∏ i in s', i := by
    have aux3 : p ∈ s' := by
      have hhhh:= h p pp
      simp [s'_def]
      constructor
      apply hhhh
      apply pp
    apply Finset.dvd_prod_of_mem _ aux3
  have : p ∣ 1 := by
    convert Nat.dvd_sub' pdvd this
    simp
  show False
  have c1 : p ≤ 1 := by exact (Nat.Prime.dvd_factorial pp).mp this
  have c2 : 2 ≤ p := by exact Nat.Prime.two_le pp
  linarith

theorem bounded_of_ex_finset (Q : ℕ → Prop) :
    (∃ s : Finset ℕ, ∀ k, Q k → k ∈ s) → ∃ n, ∀ k, Q k → k < n := by
  rintro ⟨s, hs⟩
  use s.sup id + 1
  intro k Qk
  apply Nat.lt_succ_of_le
  show id k ≤ s.sup id
  apply le_sup (hs k Qk)

theorem ex_finset_of_bounded (Q : ℕ → Prop) [DecidablePred Q] :
    (∃ n, ∀ k, Q k → k ≤ n) → ∃ s : Finset ℕ, ∀ k, Q k ↔ k ∈ s := by
  rintro ⟨n, hn⟩
  use (range (n + 1)).filter Q
  intro k
  simp [Nat.lt_succ_iff]
  exact hn k

example : 27 % 4 = 3 := by norm_num

example (n : ℕ) : (4 * n + 3) % 4 = 3 := by
  rw [add_comm, Nat.add_mul_mod_self_left]

theorem mod_4_eq_3_or_mod_4_eq_3 {m n : ℕ} (h : m * n % 4 = 3) : m % 4 = 3 ∨ n % 4 = 3 := by
  revert h
  rw [Nat.mul_mod]
  have : m % 4 < 4 := Nat.mod_lt m (by norm_num)
  interval_cases m % 4 <;> simp [-Nat.mul_mod_mod]
  have : n % 4 < 4 := Nat.mod_lt n (by norm_num)
  interval_cases n % 4 <;> simp

theorem two_le_of_mod_4_eq_3 {n : ℕ} (h : n % 4 = 3) : 2 ≤ n := by
  apply two_le <;>
    · intro neq
      rw [neq] at h
      norm_num at h

theorem aux {m n : ℕ} (h₀ : m ∣ n) (h₁ : 2 ≤ m) (h₂ : m < n) : n / m ∣ n ∧ n / m < n := by
  have rr : n / m ∣ n := by
    use m
    apply Eq.symm
    have r := Nat.div_mul_cancel h₀
    apply r
  constructor
  apply rr
  apply Nat.div_lt_self
  linarith
  linarith

theorem exists_prime_factor_mod_4_eq_3 {n : Nat} (h : n % 4 = 3) :
    ∃ p : Nat, p.Prime ∧ p ∣ n ∧ p % 4 = 3 := by
  by_cases np : n.Prime
  · use n
  induction' n using Nat.strong_induction_on with n ih
  rw [Nat.prime_def_lt] at np
  push_neg at np
  rcases np (two_le_of_mod_4_eq_3 h) with ⟨m, mltn, mdvdn, mne1⟩
  have mge2 : 2 ≤ m := by
    apply two_le _ mne1
    intro mz
    rw [mz, zero_dvd_iff] at mdvdn
    linarith
  have neq : m * (n / m) = n := Nat.mul_div_cancel' mdvdn
  have : m % 4 = 3 ∨ n / m % 4 = 3 := by
    apply mod_4_eq_3_or_mod_4_eq_3
    rw [neq, h]
  rcases this with h1 | h1
  . by_cases mp : m.Prime
    . use m
    have h2 := ih m mltn h1 mp
    rcases h2 with ⟨p, ⟨hq1, ⟨hq2, hq3⟩⟩⟩
    have hq4 : p ∣ n := by exact Nat.dvd_trans hq2 mdvdn
    use p
  . by_cases mp : (n / m).Prime
    . use (n / m)
      constructor
      apply mp
      constructor
      use m
      linarith[neq]
      apply h1
    have h3 : n / m < n := by
      refine Nat.div_lt_of_lt_mul ?h
      have rrrr: 0 < n := by linarith
      exact (Nat.lt_mul_iff_one_lt_left rrrr).mpr mge2
    have h2 := ih (n / m) h3 h1 mp
    rcases h2 with ⟨p, ⟨hq1, ⟨hq2, hq3⟩⟩⟩
    use p
    constructor
    assumption
    constructor
    have rrrr2 : n / m ∣ n := by
      use m
      apply symm
      rw [mul_comm]
      apply neq
    exact Nat.dvd_trans hq2 rrrr2
    assumption


example (m n : ℕ) (s : Finset ℕ) (h : m ∈ erase s n) : m ≠ n ∧ m ∈ s := by
  rwa [mem_erase] at h

example (m n : ℕ) (s : Finset ℕ) (h : m ∈ erase s n) : m ≠ n ∧ m ∈ s := by
  simp at h
  assumption

theorem primes_mod_4_eq_3_infinite : ∀ n, ∃ p > n, Nat.Prime p ∧ p % 4 = 3 := by
  by_contra h
  push_neg at h
  rcases h with ⟨n, hn⟩
  have : ∃ s : Finset Nat, ∀ p : ℕ, p.Prime ∧ p % 4 = 3 ↔ p ∈ s := by
    apply ex_finset_of_bounded
    use n
    contrapose! hn
    rcases hn with ⟨p, ⟨pp, p4⟩, pltn⟩
    exact ⟨p, pltn, pp, p4⟩
  rcases this with ⟨s, hs⟩
  have h₁ : ((4 * ∏ i in erase s 3, i) + 3) % 4 = 3 := by
    rw [add_comm, Nat.add_mul_mod_self_left]
  rcases exists_prime_factor_mod_4_eq_3 h₁ with ⟨p, pp, pdvd, p4eq⟩
  have ps : p ∈ s := by
    have curr_aux : Nat.Prime p ∧ p % 4 = 3 := by
      constructor
      apply pp
      apply p4eq
    have curr := (hs p).mp curr_aux
    apply curr
  have pne3 : p ≠ 3 := by
    intro h
    have rr : Nat.gcd 3 4 = 1 := by norm_num
    rw [h] at pdvd
    have pdvd2 : 3 ∣ 4 * ∏ i ∈ s.erase 3, i := by
      obtain ⟨k, hk⟩ := pdvd
      use (k - 1)
      calc
        4 * ∏ i ∈ s.erase 3, i = 4 * ∏ i ∈ s.erase 3, i + 3 - 3 := by rfl
        _ = 3 * k - 3 := by rw [hk]
        _ = 3 * (k - 1) := by exact Eq.symm (Nat.mul_sub_one 3 k)
    have pdvd3 : 3 ∣ ∏ i ∈ s.erase 3, i := by exact Nat.Coprime.dvd_of_dvd_mul_left rr pdvd2
    have qqq : ∀ n ∈ s.erase 3, Nat.Prime n := by
      intro n
      intro hhhh
      simp at hhhh
      push_neg at hhhh
      have hhhh2 := hhhh.2
      have hhhh3 := ((hs n).mpr hhhh2).1
      apply hhhh3
    have mm := mem_of_dvd_prod_primes pp qqq
    rw [h] at mm
    have mm2 := mm pdvd3
    simp at mm2
  have : p ∣ 4 * ∏ i in erase s 3, i := by
    have aux : p ∣ ∏ i in erase s 3, i := by
      have aux2 : p ∈ erase s 3 := by
        simp
        push_neg
        constructor
        apply pne3
        apply ps
      apply Finset.dvd_prod_of_mem _ aux2
    exact Dvd.dvd.mul_left aux 4
  have : p ∣ 3 := by
    exact (Nat.dvd_add_iff_right this).mpr pdvd
  have : p = 3 := by
    refine Nat.Prime.eq_of_dvd_of_prime pp ?prime_q this
    exact Nat.prime_three
  contradiction
