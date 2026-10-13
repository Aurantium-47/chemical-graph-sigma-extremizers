import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

namespace W03

noncomputable def powerT (n : ℕ) : ℝ := Real.rpow 2 (1 / (n : ℝ))

noncomputable def powerS (n : ℕ) : ℝ := Real.rpow 3 (1 / (n : ℝ))

noncomputable def powerD (n : ℕ) : ℝ := 1 + 2 * powerT n - powerS n

noncomputable def powerDelta (n : ℕ) : ℝ :=
  (n : ℝ) * (powerS n - 1) / (2 * powerD n)

theorem reciprocal_exponent_bounds {n : ℕ} (hn : 2 ≤ n) :
    0 < 1 / (n : ℝ) ∧ 1 / (n : ℝ) < 1 := by
  have hnr : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpos : (0 : ℝ) < (n : ℝ) := by linarith
  exact ⟨div_pos zero_lt_one hpos, (div_lt_one hpos).mpr (by linarith)⟩

theorem power_basic_bounds {n : ℕ} (hn : 2 ≤ n) :
    1 < powerT n ∧ powerT n < 2 ∧ powerT n < powerS n := by
  have hp := reciprocal_exponent_bounds hn
  unfold powerT powerS
  refine ⟨Real.one_lt_rpow (by norm_num) hp.1, ?_, ?_⟩
  · simpa only [Real.rpow_one] using
      (Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hp.2)
  · exact Real.rpow_lt_rpow (by norm_num) (by norm_num) hp.1

theorem powerD_gt_two {n : ℕ} (hn : 2 ≤ n) : 2 < powerD n := by
  have hp := reciprocal_exponent_bounds hn
  have hmid := (Real.strictConcaveOn_rpow hp.1 hp.2).2
    (x := (1 : ℝ)) (by norm_num) (y := (3 : ℝ)) (by norm_num)
    (by norm_num) (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  unfold powerD powerT powerS
  norm_num [smul_eq_mul, Real.one_rpow] at hmid ⊢
  linarith

theorem scaled_powerS_sub_one_lt_two {n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ) * (powerS n - 1) < 2 := by
  have hp := reciprocal_exponent_bounds hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hnp : (n : ℝ) * (1 / (n : ℝ)) = 1 := mul_one_div_cancel hnpos.ne'
  have hb := Real.rpow_one_add_lt_one_add_mul_self
    (s := (2 : ℝ)) (by norm_num) (by norm_num) hp.1 hp.2
  rw [show (1 : ℝ) + 2 = 3 from by norm_num] at hb
  change powerS n < 1 + (1 / (n : ℝ)) * 2 at hb
  have hmult := mul_lt_mul_of_pos_left hb hnpos
  nlinarith only [hmult, hnp]

theorem powerDelta_bounds {n : ℕ} (hn : 2 ≤ n) :
    0 < powerDelta n ∧ powerDelta n < 1 / 2 := by
  have ht := power_basic_bounds hn
  have hd := powerD_gt_two hn
  have hb := scaled_powerS_sub_one_lt_two hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hden : 0 < 2 * powerD n := by linarith
  unfold powerDelta
  constructor
  · exact div_pos (mul_pos hnpos (sub_pos.mpr (lt_trans ht.1 ht.2.2))) hden
  · apply (div_lt_iff₀ hden).mpr
    nlinarith only [hb, hd]

theorem real_power_bounds {n : ℕ} (hn : 2 ≤ n) :
    1 < powerT n ∧ powerT n < 2 ∧ powerT n < powerS n ∧
    2 < powerD n ∧ (n : ℝ) * (powerS n - 1) < 2 ∧
    0 < powerDelta n ∧ powerDelta n < 1 / 2 := by
  obtain ⟨ht1, ht2, hts⟩ := power_basic_bounds hn
  obtain ⟨hd1, hd2⟩ := powerDelta_bounds hn
  exact ⟨ht1, ht2, hts, powerD_gt_two hn,
    scaled_powerS_sub_one_lt_two hn, hd1, hd2⟩

end W03

set_option pp.all true
#print W03.powerT
#check @W03.powerT
#print axioms W03.powerT
#print W03.powerS
#check @W03.powerS
#print axioms W03.powerS
#print W03.powerD
#check @W03.powerD
#print axioms W03.powerD
#print W03.powerDelta
#check @W03.powerDelta
#print axioms W03.powerDelta
#check @W03.reciprocal_exponent_bounds
#print axioms W03.reciprocal_exponent_bounds
#check @W03.power_basic_bounds
#print axioms W03.power_basic_bounds
#check @W03.powerD_gt_two
#print axioms W03.powerD_gt_two
#check @W03.scaled_powerS_sub_one_lt_two
#print axioms W03.scaled_powerS_sub_one_lt_two
#check @W03.powerDelta_bounds
#print axioms W03.powerDelta_bounds
#check @W03.real_power_bounds
#print axioms W03.real_power_bounds
