import W03.FinalCoordinates

namespace W03

def Chemical {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  G.Connected ∧ ∀ x, vertexDegree G x ≤ 4

/-- Comparison with every same-order connected simple graph of maximum degree four. -/
def Maximizes {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ H : SimpleGraph (Fin n), Chemical H → totalIndex H ≤ totalIndex G

theorem graph_global_bound_and_equality {n : ℕ} (hn : 7 ≤ n)
    (G : SimpleGraph (Fin n)) (hc : G.Connected)
    (hmax : ∀ x, vertexDegree G x ≤ 4) :
    totalIndex G ≤ extremalValue n ∧
    (totalIndex G = extremalValue n ↔ WinnerProfile n (graphProfile G)) := by
  have hgraph := graph_index_le_parityUpper hn G hc hmax
  have hscalar := parityUpper_global_max hn (degreeS G)
  have hcon := chemical_penalty_congruences hn G hc hmax
  have hsum := chemical_multiplicities_sum hn G hc hmax
  refine ⟨le_trans hgraph.1 hscalar.1, ?_⟩
  have hchain : totalIndex G = extremalValue n ↔
      degreeS G = winningCandidate n ∧
      degreePenalty n (degreeU G) (degreeV G) = parityPenaltyFloor n (degreeS G) := by
    constructor
    · intro he
      have hu : parityUpper n (degreeS G) = extremalValue n :=
        le_antisymm hscalar.1 (by rw [← he]; exact hgraph.1)
      exact ⟨hscalar.2.mp hu, hgraph.2.mp (he.trans hu.symm)⟩
    · rintro ⟨hs, hp⟩
      exact (hgraph.2.mpr hp).trans (hscalar.2.mpr hs)
  exact hchain.trans ((winning_coordinates_iff hn (degreeS G) (degreeU G) (degreeV G) hcon).trans
    (graph_coordinates_iff_winner G hsum))

theorem winner_profile_attains_bound (n : ℕ) (hn : 7 ≤ n) (p : Fin 4 → ℕ)
    (hp : WinnerProfile n p) :
    ∃ G : SimpleGraph (Fin n), Chemical G ∧ graphProfile G = p ∧
      totalIndex G = extremalValue n := by
  obtain ⟨G, hc, hmax, hcounts⟩ := exists_graph_of_winnerProfile n hn p hp
  have hprofile : graphProfile G = p := by
    funext i
    exact hcounts i
  have hw : WinnerProfile n (graphProfile G) := by simpa only [hprofile] using hp
  exact ⟨G, ⟨hc, hmax⟩, hprofile, (graph_global_bound_and_equality hn G hc hmax).2.mpr hw⟩

theorem exists_graph_attaining_bound (n : ℕ) (hn : 7 ≤ n) :
    ∃ G : SimpleGraph (Fin n), Chemical G ∧ totalIndex G = extremalValue n := by
  obtain ⟨p, hp⟩ := exists_winnerProfile n
  obtain ⟨G, hc, _, he⟩ := winner_profile_attains_bound n hn p hp
  exact ⟨G, hc, he⟩

theorem maximizes_iff_winnerProfile {n : ℕ} (hn : 7 ≤ n)
    (G : SimpleGraph (Fin n)) (hc : G.Connected)
    (hmax : ∀ x, vertexDegree G x ≤ 4) :
    Maximizes G ↔ WinnerProfile n (graphProfile G) := by
  have hbound := graph_global_bound_and_equality hn G hc hmax
  constructor
  · intro hm
    obtain ⟨H, hH, hHeq⟩ := exists_graph_attaining_bound n hn
    have hge : extremalValue n ≤ totalIndex G := by
      rw [← hHeq]
      exact hm H hH
    exact hbound.2.mp (le_antisymm hbound.1 hge)
  · intro hw
    have he := hbound.2.mpr hw
    intro H hH
    rw [he]
    exact (graph_global_bound_and_equality hn H hH.1 hH.2).1

theorem every_winnerProfile_has_maximizer (n : ℕ) (hn : 7 ≤ n) (p : Fin 4 → ℕ)
    (hp : WinnerProfile n p) :
    ∃ G : SimpleGraph (Fin n), Chemical G ∧ graphProfile G = p ∧
      totalIndex G = extremalValue n ∧ Maximizes G := by
  obtain ⟨G, hc, hprofile, he⟩ := winner_profile_attains_bound n hn p hp
  refine ⟨G, hc, hprofile, he, ?_⟩
  intro H hH
  rw [he]
  exact (graph_global_bound_and_equality hn H hH.1 hH.2).1

/-- The original extremal profile classification, together with attainment of every listed profile. -/
theorem chemical_conjecture10 (n : ℕ) (hn : 7 ≤ n) :
    (∀ G : SimpleGraph (Fin n), Chemical G →
      (Maximizes G ↔ WinnerProfile n (graphProfile G))) ∧
    (∀ p : Fin 4 → ℕ, WinnerProfile n p →
      ∃ G : SimpleGraph (Fin n), Chemical G ∧ graphProfile G = p ∧
        totalIndex G = extremalValue n ∧ Maximizes G) := by
  constructor
  · intro G hG
    exact maximizes_iff_winnerProfile hn G hG.1 hG.2
  · intro p hp
    exact every_winnerProfile_has_maximizer n hn p hp

end W03

set_option pp.all true
#print W03.Chemical
#check @W03.Chemical
#print axioms W03.Chemical
#print W03.Maximizes
#check @W03.Maximizes
#print axioms W03.Maximizes
#check @W03.graph_global_bound_and_equality
#print axioms W03.graph_global_bound_and_equality
#check @W03.winner_profile_attains_bound
#print axioms W03.winner_profile_attains_bound
#check @W03.exists_graph_attaining_bound
#print axioms W03.exists_graph_attaining_bound
#check @W03.maximizes_iff_winnerProfile
#print axioms W03.maximizes_iff_winnerProfile
#check @W03.every_winnerProfile_has_maximizer
#print axioms W03.every_winnerProfile_has_maximizer
#check @W03.chemical_conjecture10
#print axioms W03.chemical_conjecture10
