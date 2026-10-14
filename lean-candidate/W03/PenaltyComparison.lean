import W03.IndexDecomposition
import W03.PowerBounds

namespace W03

theorem positive_three_term_comparison (a b c x y z l m k : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hx : l ≤ x) (hy : m ≤ y) (hz : k ≤ z) :
    a * l + b * m + c * k ≤ a * x + b * y + c * z ∧
    (a * x + b * y + c * z = a * l + b * m + c * k ↔
      x = l ∧ y = m ∧ z = k) := by
  have h1 := mul_nonneg ha.le (sub_nonneg.mpr hx)
  have h2 := mul_nonneg hb.le (sub_nonneg.mpr hy)
  have h3 := mul_nonneg hc.le (sub_nonneg.mpr hz)
  have hs : a * (x - l) + b * (y - m) + c * (z - k) =
      (a * x + b * y + c * z) - (a * l + b * m + c * k) := by ring
  constructor
  · have h := add_nonneg (add_nonneg h1 h2) h3
    rw [hs] at h
    exact sub_nonneg.mp h
  constructor
  · intro he
    have hzsum : a * (x - l) + b * (y - m) + c * (z - k) = 0 := by
      rw [hs, he, sub_self]
    have h12 : a * (x - l) + b * (y - m) = 0 := by linarith only [h1, h2, h3, hzsum]
    have h1z : a * (x - l) = 0 := by linarith only [h1, h2, h12]
    have h2z : b * (y - m) = 0 := by linarith only [h1, h2, h12]
    have h3z : c * (z - k) = 0 := by linarith only [h12, hzsum]
    exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp h1z).resolve_left ha.ne'),
      sub_eq_zero.mp ((mul_eq_zero.mp h2z).resolve_left hb.ne'),
      sub_eq_zero.mp ((mul_eq_zero.mp h3z).resolve_left hc.ne')⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

noncomputable def degreePenalty (n : ℕ) (u v : ℤ) : ℝ :=
  quadraticPenalty (powerT n) (powerS n) (u : ℝ) (v : ℝ)

theorem penalty_coefficients_pos {n : ℕ} (hn : 2 ≤ n) :
    0 < powerS n - powerT n + 1 ∧ 0 < 2 - powerT n ∧
    0 < powerT n - 1 ∧ 0 < powerS n - 1 := by
  obtain ⟨ht1, ht2, hts⟩ := power_basic_bounds hn
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem penalty_three_square_comparison {n : ℕ} (hn : 2 ≤ n)
    (u v : ℤ) (l m k : ℝ)
    (hu : l ≤ (u : ℝ) ^ 2) (hv : m ≤ (v : ℝ) ^ 2)
    (hs : k ≤ ((u : ℝ) + (v : ℝ)) ^ 2) :
    (powerS n - powerT n + 1) * l + (2 - powerT n) * m +
      (powerT n - 1) * k ≤ degreePenalty n u v ∧
    (degreePenalty n u v =
      (powerS n - powerT n + 1) * l + (2 - powerT n) * m +
        (powerT n - 1) * k ↔
      (u : ℝ) ^ 2 = l ∧ (v : ℝ) ^ 2 = m ∧ ((u : ℝ) + (v : ℝ)) ^ 2 = k) := by
  obtain ⟨ha, hb, hc, _⟩ := penalty_coefficients_pos hn
  unfold degreePenalty
  simp only [quadraticPenalty_three_squares]
  exact positive_three_term_comparison _ _ _ _ _ _ _ _ _ ha hb hc hu hv hs

theorem penalty_even_square_comparison {n : ℕ} (hn : 2 ≤ n)
    (u v : ℤ) (l m k : ℝ)
    (hu : l ≤ (u : ℝ) ^ 2)
    (hv : m ≤ (u : ℝ) ^ 2 + (v : ℝ) ^ 2)
    (hs : k ≤ ((u : ℝ) + (v : ℝ)) ^ 2) :
    (powerS n - 1) * l + (2 - powerT n) * m +
      (powerT n - 1) * k ≤ degreePenalty n u v ∧
    (degreePenalty n u v =
      (powerS n - 1) * l + (2 - powerT n) * m + (powerT n - 1) * k ↔
      (u : ℝ) ^ 2 = l ∧ (u : ℝ) ^ 2 + (v : ℝ) ^ 2 = m ∧
        ((u : ℝ) + (v : ℝ)) ^ 2 = k) := by
  obtain ⟨_, hb, hc, ha⟩ := penalty_coefficients_pos hn
  have he : degreePenalty n u v =
      (powerS n - 1) * (u : ℝ) ^ 2 +
      (2 - powerT n) * ((u : ℝ) ^ 2 + (v : ℝ) ^ 2) +
      (powerT n - 1) * ((u : ℝ) + (v : ℝ)) ^ 2 := by
    unfold degreePenalty quadraticPenalty
    ring
  simp only [he]
  exact positive_three_term_comparison _ _ _ _ _ _ _ _ _ ha hb hc hu hv hs

end W03

set_option pp.all true
#check @W03.positive_three_term_comparison
#print axioms W03.positive_three_term_comparison
#print W03.degreePenalty
#check @W03.degreePenalty
#print axioms W03.degreePenalty
#check @W03.penalty_coefficients_pos
#print axioms W03.penalty_coefficients_pos
#check @W03.penalty_three_square_comparison
#print axioms W03.penalty_three_square_comparison
#check @W03.penalty_even_square_comparison
#print axioms W03.penalty_even_square_comparison
