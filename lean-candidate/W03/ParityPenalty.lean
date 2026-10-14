import W03.PenaltyComparison

namespace W03

def PenaltyCongruences (n : ℕ) (s u v : ℤ) : Prop :=
  u % 2 = s % 2 ∧ v % 2 = ((n : ℤ) - s) % 2 ∧
    (u - v) % 4 = (-(n : ℤ)) % 4

theorem chemical_penalty_congruences {n : ℕ} (hn : 7 ≤ n)
    (G : SimpleGraph (Fin n)) (hc : G.Connected)
    (hmax : ∀ x, vertexDegree G x ≤ 4) :
    PenaltyCongruences n (degreeS G) (degreeU G) (degreeV G) :=
  chemical_profile_congruences hn G hc hmax

theorem int_square_zero_iff (u : ℤ) : (u : ℝ) ^ 2 = 0 ↔ u = 0 := by
  constructor
  · intro h
    have hz : (u : ℝ) = 0 := sq_eq_zero_iff.mp h
    exact_mod_cast hz
  · rintro rfl
    norm_num

theorem int_square_one_iff (u : ℤ) : (u : ℝ) ^ 2 = 1 ↔ u = 1 ∨ u = -1 := by
  constructor
  · intro h
    have hi : u ^ 2 = 1 := by exact_mod_cast h
    have hp : (u - 1) * (u + 1) = 0 := by nlinarith only [hi]
    rcases mul_eq_zero.mp hp with hp | hp
    · left; omega
    · right; omega
  · rintro (rfl | rfl) <;> norm_num

theorem int_square_four_iff (u : ℤ) : (u : ℝ) ^ 2 = 4 ↔ u = 2 ∨ u = -2 := by
  constructor
  · intro h
    have hi : u ^ 2 = 4 := by exact_mod_cast h
    have hp : (u - 2) * (u + 2) = 0 := by nlinarith only [hi]
    rcases mul_eq_zero.mp hp with hp | hp
    · left; omega
    · right; omega
  · rintro (rfl | rfl) <;> norm_num

theorem int_square_ge_one_of_odd (u : ℤ) (h : u % 2 = 1) :
    (1 : ℝ) ≤ (u : ℝ) ^ 2 := by
  have hn : u ≠ 0 := by omega
  have hp : 0 < u ^ 2 := sq_pos_of_ne_zero hn
  have hi : (1 : ℤ) ≤ u ^ 2 := by omega
  exact_mod_cast hi

theorem int_square_ge_four_of_even_ne_zero (u : ℤ)
    (he : u % 2 = 0) (hn : u ≠ 0) : (4 : ℝ) ≤ (u : ℝ) ^ 2 := by
  have h : u ≤ -2 ∨ 2 ≤ u := by omega
  have hi : (4 : ℤ) ≤ u ^ 2 := by
    rcases h with h | h
    · nlinarith [sq_nonneg (u + 2)]
    · nlinarith [sq_nonneg (u - 2)]
  exact_mod_cast hi

theorem int_square_ge_four_of_mod_four (u : ℤ) (h : u % 4 = 2) :
    (4 : ℝ) ≤ (u : ℝ) ^ 2 :=
  int_square_ge_four_of_even_ne_zero u (by omega) (by omega)

theorem penalty_row_zero_even {n : ℕ} (hn : 2 ≤ n) (u v : ℤ) :
    0 ≤ degreePenalty n u v ∧
    (degreePenalty n u v = 0 ↔ u = 0 ∧ v = 0) := by
  have hbase := penalty_three_square_comparison hn u v 0 0 0
    (sq_nonneg _) (sq_nonneg _) (sq_nonneg _)
  have hbound : (powerS n - powerT n + 1) * 0 + (2 - powerT n) * 0 +
      (powerT n - 1) * 0 = 0 := by ring
  simp only [hbound] at hbase
  refine ⟨hbase.1, hbase.2.trans ?_⟩
  constructor
  · rintro ⟨hu, hv, _⟩
    exact ⟨(int_square_zero_iff u).mp hu, (int_square_zero_iff v).mp hv⟩
  · rintro ⟨rfl, rfl⟩
    norm_num

theorem penalty_row_zero_odd {n : ℕ} (hn : 7 ≤ n) (s u v : ℤ)
    (h : PenaltyCongruences n s u v) (hnr : n % 4 = 0) (hsr : s % 2 = 1) :
    powerS n + 2 * powerT n - 1 ≤ degreePenalty n u v ∧
    (degreePenalty n u v = powerS n + 2 * powerT n - 1 ↔ (u = 1 ∧ v = 1) ∨ (u = -1 ∧ v = -1)) := by
  rcases h with ⟨hup, hvp, hdiff⟩
  have hu : (1 : ℝ) ≤ (u : ℝ) ^ 2 := int_square_ge_one_of_odd u (by omega)
  have hv : (1 : ℝ) ≤ (v : ℝ) ^ 2 := int_square_ge_one_of_odd v (by omega)
  have hs : (4 : ℝ) ≤ ((u : ℝ) + (v : ℝ)) ^ 2 := by
    simpa only [Int.cast_add] using int_square_ge_four_of_mod_four (u + v) (by omega)
  have hbase := penalty_three_square_comparison (by omega : 2 ≤ n) u v 1 1 4 hu hv hs
  have hbound : (powerS n - powerT n + 1) * 1 + (2 - powerT n) * 1 +
      (powerT n - 1) * 4 = powerS n + 2 * powerT n - 1 := by ring
  simp only [hbound] at hbase
  refine ⟨hbase.1, hbase.2.trans ?_⟩
  constructor
  · rintro ⟨heU, heV, heSum⟩
    rcases (int_square_one_iff u).mp heU with hu1 | hu1 <;>
      rcases (int_square_one_iff v).mp heV with hv1 | hv1 <;>
      subst u <;> subst v <;> norm_num at heSum ⊢
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num

theorem penalty_row_one_even {n : ℕ} (hn : 7 ≤ n) (s u v : ℤ)
    (h : PenaltyCongruences n s u v) (hnr : n % 4 = 1) (hsr : s % 2 = 0) :
    1 ≤ degreePenalty n u v ∧
    (degreePenalty n u v = 1 ↔ u = 0 ∧ v = 1) := by
  rcases h with ⟨hup, hvp, hdiff⟩
  have hu : (0 : ℝ) ≤ (u : ℝ) ^ 2 := sq_nonneg _
  have hv : (1 : ℝ) ≤ (v : ℝ) ^ 2 := int_square_ge_one_of_odd v (by omega)
  have hs : (1 : ℝ) ≤ ((u : ℝ) + (v : ℝ)) ^ 2 := by
    simpa only [Int.cast_add] using int_square_ge_one_of_odd (u + v) (by omega)
  have hbase := penalty_three_square_comparison (by omega : 2 ≤ n) u v 0 1 1 hu hv hs
  have hbound : (powerS n - powerT n + 1) * 0 + (2 - powerT n) * 1 +
      (powerT n - 1) * 1 = 1 := by ring
  simp only [hbound] at hbase
  refine ⟨hbase.1, hbase.2.trans ?_⟩
  constructor
  · rintro ⟨heU, heV, heSum⟩
    have hu0 : u = 0 := (int_square_zero_iff u).mp heU
    have hv1 := (int_square_one_iff v).mp heV
    have hvexact : v = 1 := by omega
    exact ⟨hu0, hvexact⟩
  · rintro ⟨rfl, rfl⟩
    norm_num

theorem penalty_row_one_odd {n : ℕ} (hn : 7 ≤ n) (s u v : ℤ)
    (h : PenaltyCongruences n s u v) (hnr : n % 4 = 1) (hsr : s % 2 = 1) :
    powerS n ≤ degreePenalty n u v ∧
    (degreePenalty n u v = powerS n ↔ u = -1 ∧ v = 0) := by
  rcases h with ⟨hup, hvp, hdiff⟩
  have hu : (1 : ℝ) ≤ (u : ℝ) ^ 2 := int_square_ge_one_of_odd u (by omega)
  have hv : (0 : ℝ) ≤ (v : ℝ) ^ 2 := sq_nonneg _
  have hs : (1 : ℝ) ≤ ((u : ℝ) + (v : ℝ)) ^ 2 := by
    simpa only [Int.cast_add] using int_square_ge_one_of_odd (u + v) (by omega)
  have hbase := penalty_three_square_comparison (by omega : 2 ≤ n) u v 1 0 1 hu hv hs
  have hbound : (powerS n - powerT n + 1) * 1 + (2 - powerT n) * 0 +
      (powerT n - 1) * 1 = powerS n := by ring
  simp only [hbound] at hbase
  refine ⟨hbase.1, hbase.2.trans ?_⟩
  constructor
  · rintro ⟨heU, heV, heSum⟩
    have hv0 : v = 0 := (int_square_zero_iff v).mp heV
    have hu1 := (int_square_one_iff u).mp heU
    have huexact : u = -1 := by omega
    exact ⟨huexact, hv0⟩
  · rintro ⟨rfl, rfl⟩
    norm_num

theorem penalty_row_two_odd {n : ℕ} (hn : 7 ≤ n) (s u v : ℤ)
    (h : PenaltyCongruences n s u v) (hnr : n % 4 = 2) (hsr : s % 2 = 1) :
    powerS n + 3 - 2 * powerT n ≤ degreePenalty n u v ∧
    (degreePenalty n u v = powerS n + 3 - 2 * powerT n ↔ (u = 1 ∧ v = -1) ∨ (u = -1 ∧ v = 1)) := by
  rcases h with ⟨hup, hvp, hdiff⟩
  have hu : (1 : ℝ) ≤ (u : ℝ) ^ 2 := int_square_ge_one_of_odd u (by omega)
  have hv : (1 : ℝ) ≤ (v : ℝ) ^ 2 := int_square_ge_one_of_odd v (by omega)
  have hs : (0 : ℝ) ≤ ((u : ℝ) + (v : ℝ)) ^ 2 := sq_nonneg _
  have hbase := penalty_three_square_comparison (by omega : 2 ≤ n) u v 1 1 0 hu hv hs
  have hbound : (powerS n - powerT n + 1) * 1 + (2 - powerT n) * 1 +
      (powerT n - 1) * 0 = powerS n + 3 - 2 * powerT n := by ring
  simp only [hbound] at hbase
  refine ⟨hbase.1, hbase.2.trans ?_⟩
  constructor
  · rintro ⟨heU, heV, heSum⟩
    rcases (int_square_one_iff u).mp heU with hu1 | hu1 <;>
      rcases (int_square_one_iff v).mp heV with hv1 | hv1 <;>
      subst u <;> subst v <;> norm_num at heSum ⊢
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num

theorem penalty_row_three_even {n : ℕ} (hn : 7 ≤ n) (s u v : ℤ)
    (h : PenaltyCongruences n s u v) (hnr : n % 4 = 3) (hsr : s % 2 = 0) :
    1 ≤ degreePenalty n u v ∧
    (degreePenalty n u v = 1 ↔ u = 0 ∧ v = -1) := by
  rcases h with ⟨hup, hvp, hdiff⟩
  have hu : (0 : ℝ) ≤ (u : ℝ) ^ 2 := sq_nonneg _
  have hv : (1 : ℝ) ≤ (v : ℝ) ^ 2 := int_square_ge_one_of_odd v (by omega)
  have hs : (1 : ℝ) ≤ ((u : ℝ) + (v : ℝ)) ^ 2 := by
    simpa only [Int.cast_add] using int_square_ge_one_of_odd (u + v) (by omega)
  have hbase := penalty_three_square_comparison (by omega : 2 ≤ n) u v 0 1 1 hu hv hs
  have hbound : (powerS n - powerT n + 1) * 0 + (2 - powerT n) * 1 +
      (powerT n - 1) * 1 = 1 := by ring
  simp only [hbound] at hbase
  refine ⟨hbase.1, hbase.2.trans ?_⟩
  constructor
  · rintro ⟨heU, heV, heSum⟩
    have hu0 : u = 0 := (int_square_zero_iff u).mp heU
    have hv1 := (int_square_one_iff v).mp heV
    have hvexact : v = -1 := by omega
    exact ⟨hu0, hvexact⟩
  · rintro ⟨rfl, rfl⟩
    norm_num

theorem penalty_row_three_odd {n : ℕ} (hn : 7 ≤ n) (s u v : ℤ)
    (h : PenaltyCongruences n s u v) (hnr : n % 4 = 3) (hsr : s % 2 = 1) :
    powerS n ≤ degreePenalty n u v ∧
    (degreePenalty n u v = powerS n ↔ u = 1 ∧ v = 0) := by
  rcases h with ⟨hup, hvp, hdiff⟩
  have hu : (1 : ℝ) ≤ (u : ℝ) ^ 2 := int_square_ge_one_of_odd u (by omega)
  have hv : (0 : ℝ) ≤ (v : ℝ) ^ 2 := sq_nonneg _
  have hs : (1 : ℝ) ≤ ((u : ℝ) + (v : ℝ)) ^ 2 := by
    simpa only [Int.cast_add] using int_square_ge_one_of_odd (u + v) (by omega)
  have hbase := penalty_three_square_comparison (by omega : 2 ≤ n) u v 1 0 1 hu hv hs
  have hbound : (powerS n - powerT n + 1) * 1 + (2 - powerT n) * 0 +
      (powerT n - 1) * 1 = powerS n := by ring
  simp only [hbound] at hbase
  refine ⟨hbase.1, hbase.2.trans ?_⟩
  constructor
  · rintro ⟨heU, heV, heSum⟩
    have hv0 : v = 0 := (int_square_zero_iff v).mp heV
    have hu1 := (int_square_one_iff u).mp heU
    have huexact : u = 1 := by omega
    exact ⟨huexact, hv0⟩
  · rintro ⟨rfl, rfl⟩
    norm_num

theorem penalty_row_two_even {n : ℕ} (hn : 7 ≤ n) (s u v : ℤ)
    (h : PenaltyCongruences n s u v) (hnr : n % 4 = 2) (hsr : s % 2 = 0) :
    4 ≤ degreePenalty n u v ∧
    (degreePenalty n u v = 4 ↔ u = 0 ∧ (v = 2 ∨ v = -2)) := by
  rcases h with ⟨hup, hvp, hdiff⟩
  have hu : (0 : ℝ) ≤ (u : ℝ) ^ 2 := sq_nonneg _
  have hv : (4 : ℝ) ≤ (u : ℝ) ^ 2 + (v : ℝ) ^ 2 := by
    by_cases hu0 : u = 0
    · have hv4 := int_square_ge_four_of_mod_four v (by omega)
      simpa [hu0] using hv4
    · have hu4 := int_square_ge_four_of_even_ne_zero u (by omega) hu0
      linarith [sq_nonneg (v : ℝ)]
  have hs : (4 : ℝ) ≤ ((u : ℝ) + (v : ℝ)) ^ 2 := by
    simpa only [Int.cast_add] using int_square_ge_four_of_mod_four (u + v) (by omega)
  have hbase := penalty_even_square_comparison (by omega : 2 ≤ n) u v 0 4 4 hu hv hs
  have hbound : (powerS n - 1) * 0 + (2 - powerT n) * 4 +
      (powerT n - 1) * 4 = 4 := by ring
  simp only [hbound] at hbase
  refine ⟨hbase.1, hbase.2.trans ?_⟩
  constructor
  · rintro ⟨heU, heV, _⟩
    have hu0 : u = 0 := (int_square_zero_iff u).mp heU
    have hv4 : (v : ℝ) ^ 2 = 4 := by simpa [hu0] using heV
    exact ⟨hu0, (int_square_four_iff v).mp hv4⟩
  · rintro ⟨rfl, rfl | rfl⟩ <;> norm_num

end W03

set_option pp.all true
#print W03.PenaltyCongruences
#check @W03.PenaltyCongruences
#print axioms W03.PenaltyCongruences
#check @W03.chemical_penalty_congruences
#print axioms W03.chemical_penalty_congruences
#check @W03.int_square_zero_iff
#print axioms W03.int_square_zero_iff
#check @W03.int_square_one_iff
#print axioms W03.int_square_one_iff
#check @W03.int_square_four_iff
#print axioms W03.int_square_four_iff
#check @W03.int_square_ge_one_of_odd
#print axioms W03.int_square_ge_one_of_odd
#check @W03.int_square_ge_four_of_even_ne_zero
#print axioms W03.int_square_ge_four_of_even_ne_zero
#check @W03.int_square_ge_four_of_mod_four
#print axioms W03.int_square_ge_four_of_mod_four
#check @W03.penalty_row_zero_even
#print axioms W03.penalty_row_zero_even
#check @W03.penalty_row_zero_odd
#print axioms W03.penalty_row_zero_odd
#check @W03.penalty_row_one_even
#print axioms W03.penalty_row_one_even
#check @W03.penalty_row_one_odd
#print axioms W03.penalty_row_one_odd
#check @W03.penalty_row_two_odd
#print axioms W03.penalty_row_two_odd
#check @W03.penalty_row_three_even
#print axioms W03.penalty_row_three_even
#check @W03.penalty_row_three_odd
#print axioms W03.penalty_row_three_odd
#check @W03.penalty_row_two_even
#print axioms W03.penalty_row_two_even
