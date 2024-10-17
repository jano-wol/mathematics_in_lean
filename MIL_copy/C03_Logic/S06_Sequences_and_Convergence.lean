import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S06

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext u v
  ring

example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_right _).2 h
  · rw [one_mul]
  exact lt_trans zero_lt_one h

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun _ : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n _
  rw [sub_self, abs_zero]
  apply εpos

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n hn
  have hns := le_of_max_le_left hn
  have hnt := le_of_max_le_right hn
  have hS := hs n hns
  have hT := ht n hnt
  have t1 : |s n + t n - (a + b)| = |(s n - a) + (t n - b)| := by
    congr
    ring
  rw [t1]
  calc
    |s n - a + (t n - b)| ≤ |s n - a| + |t n - b| := abs_add_le (s n - a) (t n - b)
    _ < (ε / 2) + (ε / 2) := by rel[hS, hT]
    _ = ε := by ring

lemma lem1 (a b : ℝ) (hb : b ≠ 0) : b * (a / b) = a := mul_div_cancel₀ a hb
lemma lem2 (a b : ℝ) (hb : |b| ≠ 0) : |b| * (a / |b|) = a := by
  have hy := lem1 a |b|
  apply hy
  apply hb

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  intro ε εpos
  have εcpos : 0 < ε / |c| := div_pos εpos acpos
  rcases cs (ε / |c|) εcpos with ⟨Ns, hs⟩
  dsimp
  use Ns
  intro n
  intro lim
  have rew : |c * s n - c * a| = |c| * |s n - a| := by
    calc
      |c * s n - c * a| = |c * (s n - a)| := by congr; ring
      _ = |c| * |s n - a| := abs_mul c (s n - a)
  rw [rew]
  have hS := hs n lim
  have hne : |c| ≠ 0 := abs_ne_zero.mpr h
  have he : |c| * (ε / |c|) = ε := lem2 ε c hne
  calc
    |c| * |s n - a| < |c| * (ε / |c|) := by rel [hS]
    _ = ε := by rw [he]


theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n hn
  have h1 := h n hn
  have h2 : |s n - a + a| ≤ |s n - a| + |a| := abs_add_le (s n - a) a
  calc
    |s n| = |s n - a + a| := by congr; ring
    _ ≤ |s n - a| + |a| := h2
    _ < 1 + |a| := by rel [h1]
    _ = |a| + 1 := by ring


theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  use max N₀ N₁
  intro n hn
  have hns := le_of_max_le_left hn
  have hnt := le_of_max_le_right hn
  have h1 := h₀ n hns
  have h2 := h₁ n hnt
  have h6 : B ≠ 0 := Ne.symm (ne_of_lt Bpos)
  have h3 : |t n| < ε / B := by
    calc
      |t n| = |t n - 0| := by congr;ring;
      _ < ε / B := h2
  by_cases h4 : s n = 0
  calc
    |s n * t n - 0| = |0 * t n - 0| := by rw [h4];
    _ = |0| := by congr;ring;
    _ = 0 := by norm_num
    _ < ε := εpos
  push_neg at h4
  by_cases h5 : t n = 0
  calc
    |s n * t n - 0| = |s n * 0 - 0| := by rw [h5];
    _ = |0| := by congr;ring;
    _ = 0 := by norm_num
    _ < ε := εpos
  calc
    |s n * t n - 0| = |s n * t n| := by congr; ring;
    _ = |s n| * |t n| := abs_mul (s n) (t n)
    _ < B * |t n| := by rel [h1]
    _ < B * (ε / B) := by rel [h3]
    _ = ε := lem1 ε B h6


theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := abs_sub_pos.mpr abne
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have hna : Na ≤ N := Nat.le_max_left Na Nb
  have hnb : Nb ≤ N := Nat.le_max_right Na Nb
  have absa : |s N - a| < ε := hNa N hna
  have absb : |s N - b| < ε := hNb N hnb
  have eqa : |a - s N| = |s N - a| := abs_sub_comm a (s N)
  have : |a - b| < |a - b| := by
    calc
      |a - b| = |(a - s N) + (s N - b)| := by congr;ring
      _  ≤ |a - s N| + |s N - b| := abs_add_le (a - s N) (s N - b)
      _ = |s N - a| + |s N - b| := by rw [eqa]
      _ < ε + ε := by rel[absa, absb]
      _ = |a - b| := by ring
  exact lt_irrefl _ this

section
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end
