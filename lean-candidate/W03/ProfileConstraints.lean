import W03.PairCounting
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

namespace W03

open scoped BigOperators Classical

theorem chemical_multiplicities_sum {n : ℕ} (hn : 7 ≤ n)
    (G : SimpleGraph (Fin n)) (hc : G.Connected)
    (hmax : ∀ x, vertexDegree G x ≤ 4) :
    degreeMultiplicity G 1 + degreeMultiplicity G 2 +
      degreeMultiplicity G 3 + degreeMultiplicity G 4 = n := by
  classical
  have hp := connected_vertexDegree_pos (by omega : 2 ≤ n) G hc
  have hm : ∀ x ∈ (Finset.univ : Finset (Fin n)),
      vertexDegree G x ∈ ({1, 2, 3, 4} : Finset ℕ) := by
    intro x _
    have hpos := hp x
    have hu := hmax x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have hs := Finset.sum_fiberwise_of_maps_to'
    (s := Finset.univ) (t := {1, 2, 3, 4}) (g := vertexDegree G)
    hm (fun _ => (1 : ℕ))
  simpa [degreeMultiplicity, add_assoc] using hs

theorem chemical_odd_multiplicities_even {n : ℕ} (hn : 7 ≤ n)
    (G : SimpleGraph (Fin n)) (hc : G.Connected)
    (hmax : ∀ x, vertexDegree G x ≤ 4) :
    Even (degreeMultiplicity G 1 + degreeMultiplicity G 3) := by
  classical
  have hp := connected_vertexDegree_pos (by omega : 2 ≤ n) G hc
  have hset : (Finset.univ.filter fun x => Odd (G.degree x)) =
      (Finset.univ.filter fun x => vertexDegree G x = 1) ∪
        (Finset.univ.filter fun x => vertexDegree G x = 3) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    rw [← vertexDegree_eq_degree G x, Nat.odd_iff]
    have hpos := hp x
    have hu := hmax x
    omega
  have hd : Disjoint (Finset.univ.filter fun x => vertexDegree G x = 1)
      (Finset.univ.filter fun x => vertexDegree G x = 3) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    omega
  have he := G.even_card_odd_degree_vertices
  rw [hset, Finset.card_union_of_disjoint hd] at he
  exact he

theorem chemical_profile_feasible {n : ℕ} (hn : 7 ≤ n)
    (G : SimpleGraph (Fin n)) (hc : G.Connected)
    (hmax : ∀ x, vertexDegree G x ≤ 4) :
    (degreeMultiplicity G 1 + degreeMultiplicity G 2 +
      degreeMultiplicity G 3 + degreeMultiplicity G 4 = n) ∧
    Even (degreeMultiplicity G 1 + degreeMultiplicity G 3) :=
  ⟨chemical_multiplicities_sum hn G hc hmax,
    chemical_odd_multiplicities_even hn G hc hmax⟩

noncomputable def degreeS {V : Type*} [Fintype V] (G : SimpleGraph V) : ℤ :=
  (degreeMultiplicity G 1 : ℤ) + (degreeMultiplicity G 4 : ℤ)

noncomputable def degreeU {V : Type*} [Fintype V] (G : SimpleGraph V) : ℤ :=
  (degreeMultiplicity G 1 : ℤ) - (degreeMultiplicity G 4 : ℤ)

noncomputable def degreeV {V : Type*} [Fintype V] (G : SimpleGraph V) : ℤ :=
  (degreeMultiplicity G 2 : ℤ) - (degreeMultiplicity G 3 : ℤ)

theorem chemical_profile_congruences {n : ℕ} (hn : 7 ≤ n)
    (G : SimpleGraph (Fin n)) (hc : G.Connected)
    (hmax : ∀ x, vertexDegree G x ≤ 4) :
    degreeU G % 2 = degreeS G % 2 ∧
    degreeV G % 2 = ((n : ℤ) - degreeS G) % 2 ∧
    (degreeU G - degreeV G) % 4 = (-(n : ℤ)) % 4 := by
  have hsum := congrArg (fun k : ℕ => (k : ℤ))
    (chemical_multiplicities_sum hn G hc hmax)
  simp only [Nat.cast_add] at hsum
  obtain ⟨k, hk⟩ := chemical_odd_multiplicities_even hn G hc hmax
  have hpar := congrArg (fun k : ℕ => (k : ℤ)) hk
  simp only [Nat.cast_add] at hpar
  unfold degreeS degreeU degreeV
  constructor
  · omega
  constructor <;> omega

end W03

set_option pp.all true
#check @W03.chemical_multiplicities_sum
#print axioms W03.chemical_multiplicities_sum
#check @W03.chemical_odd_multiplicities_even
#print axioms W03.chemical_odd_multiplicities_even
#check @W03.chemical_profile_feasible
#print axioms W03.chemical_profile_feasible
#print W03.degreeS
#check @W03.degreeS
#print axioms W03.degreeS
#print W03.degreeU
#check @W03.degreeU
#print axioms W03.degreeU
#print W03.degreeV
#check @W03.degreeV
#print axioms W03.degreeV
#check @W03.chemical_profile_congruences
#print axioms W03.chemical_profile_congruences
