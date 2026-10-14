import W03.ParityParabola
import W03.ParityPenalty

namespace W03

noncomputable def evenPenaltyBound (n : ℕ) : ℝ :=
  if n % 4 = 0 then 0 else if n % 4 = 2 then 4 else 1

noncomputable def oddPenaltyBound (n : ℕ) : ℝ :=
  if n % 4 = 0 then powerS n + 2 * powerT n - 1 else
    if n % 4 = 2 then powerS n + 3 - 2 * powerT n else powerS n

noncomputable def parityPenaltyFloor (n : ℕ) (s : ℤ) : ℝ :=
  if s % 2 = 0 then evenPenaltyBound n else oddPenaltyBound n

noncomputable def parityUpper (n : ℕ) (s : ℤ) : ℝ :=
  indexParabola n s - parityPenaltyFloor n s / 4

theorem parityUpper_even_max {n : ℕ} (hn : 7 ≤ n) (s : ℤ) (hs : s % 2 = 0) :
    parityUpper n s ≤ parityUpper n (evenCandidate n) ∧
    (parityUpper n s = parityUpper n (evenCandidate n) ↔ s = evenCandidate n) := by
  have h := even_candidate_max hn s hs
  simpa [parityUpper, parityPenaltyFloor, hs, (candidate_parities n).1] using h

theorem parityUpper_odd_max {n : ℕ} (hn : 7 ≤ n) (s : ℤ) (hs : s % 2 = 1) :
    parityUpper n s ≤ parityUpper n (oddCandidate n) ∧
    (parityUpper n s = parityUpper n (oddCandidate n) ↔ s = oddCandidate n) := by
  have h := odd_candidate_max hn s hs
  simpa [parityUpper, parityPenaltyFloor, hs, (candidate_parities n).2] using h

theorem parity_comparison_zero {n : ℕ} (hn : 7 ≤ n) (hnr : n % 4 = 0) :
    parityUpper n (evenCandidate n) - parityUpper n (oddCandidate n) =
      (4 * powerT n - (n : ℝ) * (powerS n - 1)) / 4 ∧
    parityUpper n (oddCandidate n) < parityUpper n (evenCandidate n) := by
  have hnat : n = 4 * (n / 4) + 0 := by omega
  have hreal : (n : ℝ) = 4 * ((n / 4 : ℕ) : ℝ) + 0 := by exact_mod_cast hnat
  have hp := candidate_parities n
  have he : parityUpper n (evenCandidate n) - parityUpper n (oddCandidate n) =
      (4 * powerT n - (n : ℝ) * (powerS n - 1)) / 4 := by
    simp only [parityUpper, parityPenaltyFloor, hp.1, hp.2]
    norm_num [evenPenaltyBound, oddPenaltyBound, evenCandidate, oddCandidate,
      indexParabola, hnr, powerD]
    rw [hreal]
    ring
  refine ⟨he, ?_⟩
  have ht := power_basic_bounds (by omega : 2 ≤ n)
  have hb := scaled_powerS_sub_one_lt_two (by omega : 2 ≤ n)
  have hnum : 0 < 4 * powerT n - (n : ℝ) * (powerS n - 1) := by
    nlinarith only [ht.1, hb]
  apply sub_pos.mp
  rw [he]
  exact div_pos hnum (by norm_num)

theorem parity_comparison_one {n : ℕ} (hn : 7 ≤ n) (hnr : n % 4 = 1) :
    parityUpper n (oddCandidate n) - parityUpper n (evenCandidate n) =
      ((n : ℝ) - 1) * (powerS n - 1) / 4 ∧
    parityUpper n (evenCandidate n) < parityUpper n (oddCandidate n) := by
  have hnat : n = 4 * (n / 4) + 1 := by omega
  have hreal : (n : ℝ) = 4 * ((n / 4 : ℕ) : ℝ) + 1 := by exact_mod_cast hnat
  have hp := candidate_parities n
  have he : parityUpper n (oddCandidate n) - parityUpper n (evenCandidate n) =
      ((n : ℝ) - 1) * (powerS n - 1) / 4 := by
    simp only [parityUpper, parityPenaltyFloor, hp.1, hp.2]
    norm_num [evenPenaltyBound, oddPenaltyBound, evenCandidate, oddCandidate,
      indexParabola, hnr, powerD]
    rw [hreal]
    ring
  refine ⟨he, ?_⟩
  have ht := power_basic_bounds (by omega : 2 ≤ n)
  have hnr1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hnum : 0 < ((n : ℝ) - 1) * (powerS n - 1) :=
    mul_pos (sub_pos.mpr hnr1) (sub_pos.mpr (lt_trans ht.1 ht.2.2))
  apply sub_pos.mp
  rw [he]
  exact div_pos hnum (by norm_num)

theorem parity_comparison_two {n : ℕ} (hn : 7 ≤ n) (hnr : n % 4 = 2) :
    parityUpper n (oddCandidate n) - parityUpper n (evenCandidate n) =
      (2 * powerD n - (n : ℝ) * (powerS n - 1)) / 4 ∧
    parityUpper n (evenCandidate n) < parityUpper n (oddCandidate n) := by
  have hnat : n = 4 * (n / 4) + 2 := by omega
  have hreal : (n : ℝ) = 4 * ((n / 4 : ℕ) : ℝ) + 2 := by exact_mod_cast hnat
  have hp := candidate_parities n
  have he : parityUpper n (oddCandidate n) - parityUpper n (evenCandidate n) =
      (2 * powerD n - (n : ℝ) * (powerS n - 1)) / 4 := by
    simp only [parityUpper, parityPenaltyFloor, hp.1, hp.2]
    norm_num [evenPenaltyBound, oddPenaltyBound, evenCandidate, oddCandidate,
      indexParabola, hnr, powerD]
    rw [hreal]
    ring
  refine ⟨he, ?_⟩
  have ht := power_basic_bounds (by omega : 2 ≤ n)
  have hb := scaled_powerS_sub_one_lt_two (by omega : 2 ≤ n)
  have hd := powerD_gt_two (by omega : 2 ≤ n)
  have hnum : 0 < 2 * powerD n - (n : ℝ) * (powerS n - 1) := by
    nlinarith only [hd, hb]
  apply sub_pos.mp
  rw [he]
  exact div_pos hnum (by norm_num)

theorem parity_comparison_three {n : ℕ} (hn : 7 ≤ n) (hnr : n % 4 = 3) :
    parityUpper n (evenCandidate n) - parityUpper n (oddCandidate n) =
      ((n : ℝ) + 1) * (powerS n - 1) / 4 ∧
    parityUpper n (oddCandidate n) < parityUpper n (evenCandidate n) := by
  have hnat : n = 4 * (n / 4) + 3 := by omega
  have hreal : (n : ℝ) = 4 * ((n / 4 : ℕ) : ℝ) + 3 := by exact_mod_cast hnat
  have hp := candidate_parities n
  have he : parityUpper n (evenCandidate n) - parityUpper n (oddCandidate n) =
      ((n : ℝ) + 1) * (powerS n - 1) / 4 := by
    simp only [parityUpper, parityPenaltyFloor, hp.1, hp.2]
    norm_num [evenPenaltyBound, oddPenaltyBound, evenCandidate, oddCandidate,
      indexParabola, hnr, powerD]
    rw [hreal]
    ring
  refine ⟨he, ?_⟩
  have ht := power_basic_bounds (by omega : 2 ≤ n)
  have hnr0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hnum : 0 < ((n : ℝ) + 1) * (powerS n - 1) :=
    mul_pos (by linarith) (sub_pos.mpr (lt_trans ht.1 ht.2.2))
  apply sub_pos.mp
  rw [he]
  exact div_pos hnum (by norm_num)

theorem parityPenaltyFloor_le {n : ℕ} (hn : 7 ≤ n) (s u v : ℤ)
    (h : PenaltyCongruences n s u v) :
    parityPenaltyFloor n s ≤ degreePenalty n u v := by
  have hncases : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  have hscases : s % 2 = 0 ∨ s % 2 = 1 := by omega
  rcases hncases with hnr | hnr | hnr | hnr <;> rcases hscases with hsr | hsr
  · simpa [parityPenaltyFloor, evenPenaltyBound, oddPenaltyBound, hnr, hsr] using
      (penalty_row_zero_even (by omega : 2 ≤ n) u v).1
  · simpa [parityPenaltyFloor, evenPenaltyBound, oddPenaltyBound, hnr, hsr] using
      (penalty_row_zero_odd hn s u v h hnr hsr).1
  · simpa [parityPenaltyFloor, evenPenaltyBound, oddPenaltyBound, hnr, hsr] using
      (penalty_row_one_even hn s u v h hnr hsr).1
  · simpa [parityPenaltyFloor, evenPenaltyBound, oddPenaltyBound, hnr, hsr] using
      (penalty_row_one_odd hn s u v h hnr hsr).1
  · simpa [parityPenaltyFloor, evenPenaltyBound, oddPenaltyBound, hnr, hsr] using
      (penalty_row_two_even hn s u v h hnr hsr).1
  · simpa [parityPenaltyFloor, evenPenaltyBound, oddPenaltyBound, hnr, hsr] using
      (penalty_row_two_odd hn s u v h hnr hsr).1
  · simpa [parityPenaltyFloor, evenPenaltyBound, oddPenaltyBound, hnr, hsr] using
      (penalty_row_three_even hn s u v h hnr hsr).1
  · simpa [parityPenaltyFloor, evenPenaltyBound, oddPenaltyBound, hnr, hsr] using
      (penalty_row_three_odd hn s u v h hnr hsr).1

theorem totalIndex_eq_parabola_sub_penalty {n : ℕ} (hn : 7 ≤ n)
    (G : SimpleGraph (Fin n)) (hc : G.Connected)
    (hmax : ∀ x, vertexDegree G x ≤ 4) :
    totalIndex G = indexParabola n (degreeS G) -
      degreePenalty n (degreeU G) (degreeV G) / 4 := by
  have hd := totalIndex_decomposition hn G hc hmax
  dsimp only at hd
  unfold indexParabola degreePenalty
  simp only [powerD, powerT, powerS]
  nlinarith only [hd]

theorem graph_index_le_parityUpper {n : ℕ} (hn : 7 ≤ n)
    (G : SimpleGraph (Fin n)) (hc : G.Connected)
    (hmax : ∀ x, vertexDegree G x ≤ 4) :
    totalIndex G ≤ parityUpper n (degreeS G) ∧
    (totalIndex G = parityUpper n (degreeS G) ↔
      degreePenalty n (degreeU G) (degreeV G) = parityPenaltyFloor n (degreeS G)) := by
  have hf := parityPenaltyFloor_le hn (degreeS G) (degreeU G) (degreeV G)
    (chemical_penalty_congruences hn G hc hmax)
  simp only [totalIndex_eq_parabola_sub_penalty hn G hc hmax]
  unfold parityUpper
  constructor
  · linarith only [hf]
  constructor <;> intro h <;> linarith only [h]

end W03

set_option pp.all true
#print W03.evenPenaltyBound
#check @W03.evenPenaltyBound
#print axioms W03.evenPenaltyBound
#print W03.oddPenaltyBound
#check @W03.oddPenaltyBound
#print axioms W03.oddPenaltyBound
#print W03.parityPenaltyFloor
#check @W03.parityPenaltyFloor
#print axioms W03.parityPenaltyFloor
#print W03.parityUpper
#check @W03.parityUpper
#print axioms W03.parityUpper
#check @W03.parityUpper_even_max
#print axioms W03.parityUpper_even_max
#check @W03.parityUpper_odd_max
#print axioms W03.parityUpper_odd_max
#check @W03.parity_comparison_zero
#print axioms W03.parity_comparison_zero
#check @W03.parity_comparison_one
#print axioms W03.parity_comparison_one
#check @W03.parity_comparison_two
#print axioms W03.parity_comparison_two
#check @W03.parity_comparison_three
#print axioms W03.parity_comparison_three
#check @W03.parityPenaltyFloor_le
#print axioms W03.parityPenaltyFloor_le
#check @W03.totalIndex_eq_parabola_sub_penalty
#print axioms W03.totalIndex_eq_parabola_sub_penalty
#check @W03.graph_index_le_parityUpper
#print axioms W03.graph_index_le_parityUpper
