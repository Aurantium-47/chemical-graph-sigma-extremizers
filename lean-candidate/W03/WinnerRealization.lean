import W03.RealizationIteration

namespace W03

/-- The four residue-class rows of the degree-multiplicity table. -/
def WinnerProfile (n : ℕ) (p : Fin 4 → ℕ) : Prop :=
  (∃ k : ℕ, n = 4 * k ∧ p = profile4 k k k k) ∨
  (∃ k : ℕ, n = 4 * k + 1 ∧ p = profile4 k k k (k + 1)) ∨
  (∃ k : ℕ, n = 4 * k + 2 ∧
    (p = profile4 k (k + 1) k (k + 1) ∨ p = profile4 (k + 1) k (k + 1) k)) ∨
  (∃ k : ℕ, n = 4 * k + 3 ∧ p = profile4 (k + 1) k (k + 1) (k + 1))

theorem realizes_row_zero (k : ℕ) (hk : 2 ≤ k) :
    Realizes (4 * k) (profile4 k k k k) := by
  have hb : Realizes 8 (profile4 2 2 2 2) := ⟨base8, 0, 2, base8_certificate⟩
  have h := realizes_profile4_iterate hb (k - 2)
  have hs : 8 + 4 * (k - 2) = 4 * k := by omega
  have hl : 2 + (k - 2) = k := by omega
  simpa only [hs, hl] using h

theorem realizes_row_one (k : ℕ) (hk : 2 ≤ k) :
    Realizes (4 * k + 1) (profile4 k k k (k + 1)) := by
  have hb : Realizes 9 (profile4 2 2 2 3) := ⟨base9, 0, 2, base9_certificate⟩
  have h := realizes_profile4_iterate hb (k - 2)
  have hs : 9 + 4 * (k - 2) = 4 * k + 1 := by omega
  have hl : 2 + (k - 2) = k := by omega
  have hh : 3 + (k - 2) = k + 1 := by omega
  simpa only [hs, hl, hh] using h

theorem realizes_row_two_first (k : ℕ) (hk : 2 ≤ k) :
    Realizes (4 * k + 2) (profile4 k (k + 1) k (k + 1)) := by
  have hb : Realizes 10 (profile4 2 3 2 3) := ⟨base10A, 0, 2, base10A_certificate⟩
  have h := realizes_profile4_iterate hb (k - 2)
  have hs : 10 + 4 * (k - 2) = 4 * k + 2 := by omega
  have hl : 2 + (k - 2) = k := by omega
  have hh : 3 + (k - 2) = k + 1 := by omega
  simpa only [hs, hl, hh] using h

theorem realizes_row_two_second (k : ℕ) (hk : 2 ≤ k) :
    Realizes (4 * k + 2) (profile4 (k + 1) k (k + 1) k) := by
  have hb : Realizes 10 (profile4 3 2 3 2) := ⟨base10B, 0, 5, base10B_certificate⟩
  have h := realizes_profile4_iterate hb (k - 2)
  have hs : 10 + 4 * (k - 2) = 4 * k + 2 := by omega
  have hl : 2 + (k - 2) = k := by omega
  have hh : 3 + (k - 2) = k + 1 := by omega
  simpa only [hs, hl, hh] using h

theorem realizes_row_three (k : ℕ) (hk : 1 ≤ k) :
    Realizes (4 * k + 3) (profile4 (k + 1) k (k + 1) (k + 1)) := by
  have hb : Realizes 7 (profile4 2 1 2 2) := ⟨base7, 0, 2, base7_certificate⟩
  have h := realizes_profile4_iterate hb (k - 1)
  have hs : 7 + 4 * (k - 1) = 4 * k + 3 := by omega
  have hl : 1 + (k - 1) = k := by omega
  have hh : 2 + (k - 1) = k + 1 := by omega
  simpa only [hs, hl, hh] using h

theorem winnerProfile_realizes (n : ℕ) (hn : 7 ≤ n) (p : Fin 4 → ℕ)
    (hp : WinnerProfile n p) : Realizes n p := by
  rcases hp with h0 | h1 | h2 | h3
  · rcases h0 with ⟨k, hnk, hpk⟩
    subst n
    subst p
    exact realizes_row_zero k (by omega)
  · rcases h1 with ⟨k, hnk, hpk⟩
    subst n
    subst p
    exact realizes_row_one k (by omega)
  · rcases h2 with ⟨k, hnk, hpk⟩
    subst n
    rcases hpk with hpk | hpk
    · subst p
      exact realizes_row_two_first k (by omega)
    · subst p
      exact realizes_row_two_second k (by omega)
  · rcases h3 with ⟨k, hnk, hpk⟩
    subst n
    subst p
    exact realizes_row_three k (by omega)

/-- Every listed profile has a connected simple realization on exactly Fin n. -/
theorem exists_graph_of_winnerProfile (n : ℕ) (hn : 7 ≤ n) (p : Fin 4 → ℕ)
    (hp : WinnerProfile n p) :
    ∃ G : SimpleGraph (Fin n), G.Connected ∧
      (∀ x, vertexDegree G x ≤ 4) ∧
      (∀ i : Fin 4, degreeMultiplicity G (i.val + 1) = p i) := by
  rcases winnerProfile_realizes n hn p hp with ⟨G, u, v, hc⟩
  exact ⟨G, hc.1, hc.2.1, hc.2.2.1⟩

end W03

set_option pp.all true
#print W03.WinnerProfile
#check @W03.WinnerProfile
#print axioms W03.WinnerProfile
#check @W03.realizes_row_zero
#print axioms W03.realizes_row_zero
#check @W03.realizes_row_one
#print axioms W03.realizes_row_one
#check @W03.realizes_row_two_first
#print axioms W03.realizes_row_two_first
#check @W03.realizes_row_two_second
#print axioms W03.realizes_row_two_second
#check @W03.realizes_row_three
#print axioms W03.realizes_row_three
#check @W03.winnerProfile_realizes
#print axioms W03.winnerProfile_realizes
#check @W03.exists_graph_of_winnerProfile
#print axioms W03.exists_graph_of_winnerProfile
