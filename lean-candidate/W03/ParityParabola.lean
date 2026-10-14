import W03.PowerBounds
import Mathlib.Tactic.Ring

namespace W03

noncomputable def parabolaCenter (n : ℕ) : ℝ := (n : ℝ) / 2 + powerDelta n

noncomputable def indexParabola (n : ℕ) (s : ℤ) : ℝ :=
  ((n : ℝ) ^ 2 + 2 * (n : ℝ) * powerT n * (s : ℝ) -
    powerD n * (s : ℝ) ^ 2) / 4

def evenCandidate (n : ℕ) : ℤ :=
  if n % 4 < 2 then 2 * ((n / 4 : ℕ) : ℤ) else 2 * ((n / 4 : ℕ) : ℤ) + 2

def oddCandidate (n : ℕ) : ℤ := 2 * ((n / 4 : ℕ) : ℤ) + 1

theorem nat_int_cast_quarter (n : ℕ) :
    (((n : ℤ) / 4 : ℤ) : ℝ) = ((n / 4 : ℕ) : ℝ) := by
  have hi : (n : ℤ) / 4 = ((n / 4 : ℕ) : ℤ) := by omega
  have h := congrArg (fun z : ℤ => (z : ℝ)) hi
  simpa only [Int.cast_natCast] using h

theorem parabolaCenter_identity {n : ℕ} (hn : 2 ≤ n) :
    2 * powerD n * parabolaCenter n = 2 * (n : ℝ) * powerT n := by
  have hd := powerD_gt_two hn
  have hdn : 2 * powerD n ≠ 0 := ne_of_gt (by linarith)
  have hdelta : powerDelta n * (2 * powerD n) = (n : ℝ) * (powerS n - 1) :=
    div_mul_cancel₀ _ hdn
  calc
    2 * powerD n * parabolaCenter n =
        (n : ℝ) * powerD n + powerDelta n * (2 * powerD n) := by
      unfold parabolaCenter
      ring
    _ = (n : ℝ) * powerD n + (n : ℝ) * (powerS n - 1) := by rw [hdelta]
    _ = 2 * (n : ℝ) * powerT n := by unfold powerD; ring

theorem indexParabola_gap {n : ℕ} (hn : 2 ≤ n) (s c : ℤ) :
    indexParabola n c - indexParabola n s =
      powerD n / 4 * (((s : ℝ) - parabolaCenter n) ^ 2 -
        ((c : ℝ) - parabolaCenter n) ^ 2) := by
  have hcoef := (parabolaCenter_identity hn).symm
  simp only [indexParabola, hcoef]
  ring

theorem same_parity_square_strict (s c : ℤ) (x : ℝ)
    (hlo : (c : ℝ) - 1 < x) (hhi : x < (c : ℝ) + 1)
    (hp : s % 2 = c % 2) (hne : s ≠ c) :
    ((c : ℝ) - x) ^ 2 < ((s : ℝ) - x) ^ 2 := by
  have hsep : s ≤ c - 2 ∨ c + 2 ≤ s := by omega
  rcases hsep with hsep | hsep
  · have hs : (s : ℝ) ≤ (c : ℝ) - 2 := by exact_mod_cast hsep
    have hprod : 0 < ((c : ℝ) - (s : ℝ)) * (2 * x - (s : ℝ) - (c : ℝ)) :=
      mul_pos (by linarith) (by linarith)
    nlinarith only [hprod]
  · have hs : (c : ℝ) + 2 ≤ (s : ℝ) := by exact_mod_cast hsep
    have hprod : 0 < ((s : ℝ) - (c : ℝ)) * ((s : ℝ) + (c : ℝ) - 2 * x) :=
      mul_pos (by linarith) (by linarith)
    nlinarith only [hprod]

theorem parabola_max_of_center_window {n : ℕ} (hn : 2 ≤ n) (s c : ℤ)
    (hlo : (c : ℝ) - 1 < parabolaCenter n)
    (hhi : parabolaCenter n < (c : ℝ) + 1) (hp : s % 2 = c % 2) :
    indexParabola n s ≤ indexParabola n c ∧
    (indexParabola n s = indexParabola n c ↔ s = c) := by
  by_cases he : s = c
  · subst s
    exact ⟨le_rfl, by simp⟩
  · have hs := same_parity_square_strict s c (parabolaCenter n) hlo hhi hp he
    have hd : 0 < powerD n / 4 := div_pos (by linarith [powerD_gt_two hn]) (by norm_num)
    have hstrict : indexParabola n s < indexParabola n c := by
      apply sub_pos.mp
      rw [indexParabola_gap hn s c]
      exact mul_pos hd (sub_pos.mpr hs)
    refine ⟨hstrict.le, ?_⟩
    constructor
    · intro h
      exact False.elim (hstrict.ne h)
    · intro h
      exact False.elim (he h)

theorem candidate_parities (n : ℕ) :
    evenCandidate n % 2 = 0 ∧ oddCandidate n % 2 = 1 := by
  by_cases h : n % 4 < 2
  · simp only [evenCandidate, oddCandidate, if_pos h]
    omega
  · simp only [evenCandidate, oddCandidate, if_neg h]
    omega

theorem candidate_center_windows {n : ℕ} (hn : 2 ≤ n) :
    ((evenCandidate n : ℝ) - 1 < parabolaCenter n ∧
      parabolaCenter n < (evenCandidate n : ℝ) + 1) ∧
    ((oddCandidate n : ℝ) - 1 < parabolaCenter n ∧
      parabolaCenter n < (oddCandidate n : ℝ) + 1) := by
  have hd := powerDelta_bounds hn
  have hnat : n = 4 * (n / 4) + n % 4 := by omega
  have hreal : (n : ℝ) = 4 * ((n / 4 : ℕ) : ℝ) + ((n % 4 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hcases : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases hcases with h | h | h | h
  all_goals
    norm_num [evenCandidate, oddCandidate, parabolaCenter, h] at hreal ⊢
    simp only [nat_int_cast_quarter]
    constructor <;> constructor <;> linarith [hd.1, hd.2]

theorem candidate_interior_bounds {n : ℕ} (hn : 7 ≤ n) :
    3 ≤ evenCandidate n ∧ evenCandidate n ≤ (n : ℤ) - 3 ∧
    3 ≤ oddCandidate n ∧ oddCandidate n ≤ (n : ℤ) - 3 := by
  by_cases h : n % 4 < 2
  · simp only [evenCandidate, oddCandidate, if_pos h]
    omega
  · simp only [evenCandidate, oddCandidate, if_neg h]
    omega

theorem even_candidate_max {n : ℕ} (hn : 7 ≤ n) (s : ℤ) (hs : s % 2 = 0) :
    indexParabola n s ≤ indexParabola n (evenCandidate n) ∧
    (indexParabola n s = indexParabola n (evenCandidate n) ↔ s = evenCandidate n) := by
  have hw := (candidate_center_windows (by omega : 2 ≤ n)).1
  exact parabola_max_of_center_window (by omega : 2 ≤ n) s (evenCandidate n)
    hw.1 hw.2 (hs.trans (candidate_parities n).1.symm)

theorem odd_candidate_max {n : ℕ} (hn : 7 ≤ n) (s : ℤ) (hs : s % 2 = 1) :
    indexParabola n s ≤ indexParabola n (oddCandidate n) ∧
    (indexParabola n s = indexParabola n (oddCandidate n) ↔ s = oddCandidate n) := by
  have hw := (candidate_center_windows (by omega : 2 ≤ n)).2
  exact parabola_max_of_center_window (by omega : 2 ≤ n) s (oddCandidate n)
    hw.1 hw.2 (hs.trans (candidate_parities n).2.symm)

end W03

set_option pp.all true
#print W03.parabolaCenter
#check @W03.parabolaCenter
#print axioms W03.parabolaCenter
#print W03.indexParabola
#check @W03.indexParabola
#print axioms W03.indexParabola
#print W03.evenCandidate
#check @W03.evenCandidate
#print axioms W03.evenCandidate
#print W03.oddCandidate
#check @W03.oddCandidate
#print axioms W03.oddCandidate
#check @W03.nat_int_cast_quarter
#print axioms W03.nat_int_cast_quarter
#check @W03.parabolaCenter_identity
#print axioms W03.parabolaCenter_identity
#check @W03.indexParabola_gap
#print axioms W03.indexParabola_gap
#check @W03.same_parity_square_strict
#print axioms W03.same_parity_square_strict
#check @W03.parabola_max_of_center_window
#print axioms W03.parabola_max_of_center_window
#check @W03.candidate_parities
#print axioms W03.candidate_parities
#check @W03.candidate_center_windows
#print axioms W03.candidate_center_windows
#check @W03.candidate_interior_bounds
#print axioms W03.candidate_interior_bounds
#check @W03.even_candidate_max
#print axioms W03.even_candidate_max
#check @W03.odd_candidate_max
#print axioms W03.odd_candidate_max
