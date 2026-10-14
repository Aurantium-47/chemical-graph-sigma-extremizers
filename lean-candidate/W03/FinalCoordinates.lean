import W03.ParityComparison
import W03.WinnerRealization

namespace W03

noncomputable def graphProfile {n : ℕ} (G : SimpleGraph (Fin n)) : Fin 4 → ℕ :=
  fun i => degreeMultiplicity G (i.val + 1)

def winningCandidate (n : ℕ) : ℤ :=
  if n % 4 = 0 ∨ n % 4 = 3 then evenCandidate n else oddCandidate n

noncomputable def extremalValue (n : ℕ) : ℝ := parityUpper n (winningCandidate n)

def OptimalCoordinates (n : ℕ) (s u v : ℤ) : Prop :=
  (n % 4 = 0 ∧ s = evenCandidate n ∧ u = 0 ∧ v = 0) ∨
  (n % 4 = 1 ∧ s = oddCandidate n ∧ u = -1 ∧ v = 0) ∨
  (n % 4 = 2 ∧ s = oddCandidate n ∧
    ((u = 1 ∧ v = -1) ∨ (u = -1 ∧ v = 1))) ∨
  (n % 4 = 3 ∧ s = evenCandidate n ∧ u = 0 ∧ v = -1)

theorem graphProfile_eq_profile4_iff {n : ℕ} (G : SimpleGraph (Fin n))
    (a b c d : ℕ) :
    graphProfile G = profile4 a b c d ↔
      degreeMultiplicity G 1 = a ∧ degreeMultiplicity G 2 = b ∧
      degreeMultiplicity G 3 = c ∧ degreeMultiplicity G 4 = d := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [graphProfile, profile4] using congrFun h (0 : Fin 4)
    · simpa [graphProfile, profile4] using congrFun h (1 : Fin 4)
    · simpa [graphProfile, profile4] using congrFun h (2 : Fin 4)
    · simpa [graphProfile, profile4] using congrFun h (3 : Fin 4)
  · rintro ⟨ha, hb, hc, hd⟩
    funext i
    fin_cases i <;> simp [graphProfile, profile4, ha, hb, hc, hd]

theorem global_upper_of_even_gap {n : ℕ} (hn : 7 ≤ n)
    (hgap : parityUpper n (oddCandidate n) < parityUpper n (evenCandidate n)) (s : ℤ) :
    parityUpper n s ≤ parityUpper n (evenCandidate n) ∧
    (parityUpper n s = parityUpper n (evenCandidate n) ↔ s = evenCandidate n) := by
  by_cases hs : s % 2 = 0
  · exact parityUpper_even_max hn s hs
  · have ho : s % 2 = 1 := by omega
    have hlt := lt_of_le_of_lt (parityUpper_odd_max hn s ho).1 hgap
    exact ⟨hlt.le, ⟨fun he => False.elim (hlt.ne he),
      fun he => congrArg (parityUpper n) he⟩⟩

theorem global_upper_of_odd_gap {n : ℕ} (hn : 7 ≤ n)
    (hgap : parityUpper n (evenCandidate n) < parityUpper n (oddCandidate n)) (s : ℤ) :
    parityUpper n s ≤ parityUpper n (oddCandidate n) ∧
    (parityUpper n s = parityUpper n (oddCandidate n) ↔ s = oddCandidate n) := by
  by_cases hs : s % 2 = 1
  · exact parityUpper_odd_max hn s hs
  · have he : s % 2 = 0 := by omega
    have hlt := lt_of_le_of_lt (parityUpper_even_max hn s he).1 hgap
    exact ⟨hlt.le, ⟨fun hx => False.elim (hlt.ne hx),
      fun hx => congrArg (parityUpper n) hx⟩⟩

theorem parityUpper_global_max {n : ℕ} (hn : 7 ≤ n) (s : ℤ) :
    parityUpper n s ≤ extremalValue n ∧
    (parityUpper n s = extremalValue n ↔ s = winningCandidate n) := by
  have hcases : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases hcases with h | h | h | h
  · simpa [extremalValue, winningCandidate, h] using
      global_upper_of_even_gap hn (parity_comparison_zero hn h).2 s
  · simpa [extremalValue, winningCandidate, h] using
      global_upper_of_odd_gap hn (parity_comparison_one hn h).2 s
  · simpa [extremalValue, winningCandidate, h] using
      global_upper_of_odd_gap hn (parity_comparison_two hn h).2 s
  · simpa [extremalValue, winningCandidate, h] using
      global_upper_of_even_gap hn (parity_comparison_three hn h).2 s

theorem winning_coordinates_iff {n : ℕ} (hn : 7 ≤ n) (s u v : ℤ)
    (hcon : PenaltyCongruences n s u v) :
    (s = winningCandidate n ∧ degreePenalty n u v = parityPenaltyFloor n s) ↔
      OptimalCoordinates n s u v := by
  by_cases hs : s = winningCandidate n
  · subst s
    have hcases : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
    rcases hcases with h | h | h | h
    · simpa [OptimalCoordinates, winningCandidate, parityPenaltyFloor,
        evenPenaltyBound, oddPenaltyBound, h, (candidate_parities n).1] using
        (penalty_row_zero_even (by omega : 2 ≤ n) u v).2
    · have hc : PenaltyCongruences n (oddCandidate n) u v := by
        simpa [winningCandidate, h] using hcon
      simpa [OptimalCoordinates, winningCandidate, parityPenaltyFloor,
        evenPenaltyBound, oddPenaltyBound, h, (candidate_parities n).2] using
        (penalty_row_one_odd hn (oddCandidate n) u v hc h (candidate_parities n).2).2
    · have hc : PenaltyCongruences n (oddCandidate n) u v := by
        simpa [winningCandidate, h] using hcon
      simpa [OptimalCoordinates, winningCandidate, parityPenaltyFloor,
        evenPenaltyBound, oddPenaltyBound, h, (candidate_parities n).2] using
        (penalty_row_two_odd hn (oddCandidate n) u v hc h (candidate_parities n).2).2
    · have hc : PenaltyCongruences n (evenCandidate n) u v := by
        simpa [winningCandidate, h] using hcon
      simpa [OptimalCoordinates, winningCandidate, parityPenaltyFloor,
        evenPenaltyBound, oddPenaltyBound, h, (candidate_parities n).1] using
        (penalty_row_three_even hn (evenCandidate n) u v hc h (candidate_parities n).1).2
  · constructor
    · intro h
      exact False.elim (hs h.1)
    · intro h
      rcases h with ⟨hr, hc, _⟩ | ⟨hr, hc, _⟩ | ⟨hr, hc, _⟩ | ⟨hr, hc, _⟩
      all_goals
        exact False.elim (hs (by simpa [winningCandidate, hr] using hc))

theorem graph_coordinates_iff_winner {n : ℕ} (G : SimpleGraph (Fin n))
    (hsum : degreeMultiplicity G 1 + degreeMultiplicity G 2 +
      degreeMultiplicity G 3 + degreeMultiplicity G 4 = n) :
    OptimalCoordinates n (degreeS G) (degreeU G) (degreeV G) ↔
      WinnerProfile n (graphProfile G) := by
  constructor
  · intro h
    rcases h with ⟨hr, hs, hu, hv⟩ | ⟨hr, hs, hu, hv⟩ | ⟨hr, hs, huv⟩ |
      ⟨hr, hs, hu, hv⟩
    · left
      refine ⟨n / 4, by omega, ?_⟩
      apply (graphProfile_eq_profile4_iff G _ _ _ _).mpr
      simp [degreeS, degreeU, degreeV, evenCandidate, oddCandidate, hr] at hs hu hv
      omega
    · right; left
      refine ⟨n / 4, by omega, ?_⟩
      apply (graphProfile_eq_profile4_iff G _ _ _ _).mpr
      simp [degreeS, degreeU, degreeV, evenCandidate, oddCandidate, hr] at hs hu hv
      omega
    · rcases huv with ⟨hu, hv⟩ | ⟨hu, hv⟩
      · right; right; left
        refine ⟨n / 4, by omega, Or.inr ?_⟩
        apply (graphProfile_eq_profile4_iff G _ _ _ _).mpr
        simp [degreeS, degreeU, degreeV, evenCandidate, oddCandidate, hr] at hs hu hv
        omega
      · right; right; left
        refine ⟨n / 4, by omega, Or.inl ?_⟩
        apply (graphProfile_eq_profile4_iff G _ _ _ _).mpr
        simp [degreeS, degreeU, degreeV, evenCandidate, oddCandidate, hr] at hs hu hv
        omega
    · right; right; right
      refine ⟨n / 4, by omega, ?_⟩
      apply (graphProfile_eq_profile4_iff G _ _ _ _).mpr
      simp [degreeS, degreeU, degreeV, evenCandidate, oddCandidate, hr] at hs hu hv
      omega
  · intro h
    rcases h with ⟨k, hn, hp⟩ | ⟨k, hn, hp⟩ | ⟨k, hn, hp⟩ | ⟨k, hn, hp⟩
    · rcases (graphProfile_eq_profile4_iff G _ _ _ _).mp hp with ⟨ha, hb, hc, hd⟩
      have hr : n % 4 = 0 := by omega
      have hq : n / 4 = k := by omega
      left
      refine ⟨hr, ?_, ?_, ?_⟩ <;>
        simp [degreeS, degreeU, degreeV, evenCandidate, oddCandidate, hr, hq, ha, hb, hc, hd] <;> omega
    · rcases (graphProfile_eq_profile4_iff G _ _ _ _).mp hp with ⟨ha, hb, hc, hd⟩
      have hr : n % 4 = 1 := by omega
      have hq : n / 4 = k := by omega
      right; left
      refine ⟨hr, ?_, ?_, ?_⟩ <;>
        simp [degreeS, degreeU, degreeV, evenCandidate, oddCandidate, hr, hq, ha, hb, hc, hd] <;> omega
    · have hr : n % 4 = 2 := by omega
      have hq : n / 4 = k := by omega
      rcases hp with hp | hp
      · rcases (graphProfile_eq_profile4_iff G _ _ _ _).mp hp with ⟨ha, hb, hc, hd⟩
        right; right; left
        refine ⟨hr, ?_, Or.inr ⟨?_, ?_⟩⟩ <;>
          simp [degreeS, degreeU, degreeV, evenCandidate, oddCandidate, hr, hq, ha, hb, hc, hd] <;> omega
      · rcases (graphProfile_eq_profile4_iff G _ _ _ _).mp hp with ⟨ha, hb, hc, hd⟩
        right; right; left
        refine ⟨hr, ?_, Or.inl ⟨?_, ?_⟩⟩ <;>
          simp [degreeS, degreeU, degreeV, evenCandidate, oddCandidate, hr, hq, ha, hb, hc, hd] <;> omega
    · rcases (graphProfile_eq_profile4_iff G _ _ _ _).mp hp with ⟨ha, hb, hc, hd⟩
      have hr : n % 4 = 3 := by omega
      have hq : n / 4 = k := by omega
      right; right; right
      refine ⟨hr, ?_, ?_, ?_⟩ <;>
        simp [degreeS, degreeU, degreeV, evenCandidate, oddCandidate, hr, hq, ha, hb, hc, hd] <;> omega

theorem exists_winnerProfile (n : ℕ) : ∃ p : Fin 4 → ℕ, WinnerProfile n p := by
  have hcases : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases hcases with h | h | h | h
  · refine ⟨profile4 (n / 4) (n / 4) (n / 4) (n / 4), Or.inl ⟨n / 4, ?_, rfl⟩⟩
    omega
  · refine ⟨profile4 (n / 4) (n / 4) (n / 4) (n / 4 + 1),
      Or.inr (Or.inl ⟨n / 4, ?_, rfl⟩)⟩
    omega
  · refine ⟨profile4 (n / 4) (n / 4 + 1) (n / 4) (n / 4 + 1),
      Or.inr (Or.inr (Or.inl ⟨n / 4, ?_, Or.inl rfl⟩))⟩
    omega
  · refine ⟨profile4 (n / 4 + 1) (n / 4) (n / 4 + 1) (n / 4 + 1),
      Or.inr (Or.inr (Or.inr ⟨n / 4, ?_, rfl⟩))⟩
    omega

end W03

set_option pp.all true
#print W03.graphProfile
#check @W03.graphProfile
#print axioms W03.graphProfile
#print W03.winningCandidate
#check @W03.winningCandidate
#print axioms W03.winningCandidate
#print W03.extremalValue
#check @W03.extremalValue
#print axioms W03.extremalValue
#print W03.OptimalCoordinates
#check @W03.OptimalCoordinates
#print axioms W03.OptimalCoordinates
#check @W03.graphProfile_eq_profile4_iff
#print axioms W03.graphProfile_eq_profile4_iff
#check @W03.global_upper_of_even_gap
#print axioms W03.global_upper_of_even_gap
#check @W03.global_upper_of_odd_gap
#print axioms W03.global_upper_of_odd_gap
#check @W03.parityUpper_global_max
#print axioms W03.parityUpper_global_max
#check @W03.winning_coordinates_iff
#print axioms W03.winning_coordinates_iff
#check @W03.graph_coordinates_iff_winner
#print axioms W03.graph_coordinates_iff_winner
#check @W03.exists_winnerProfile
#print axioms W03.exists_winnerProfile
