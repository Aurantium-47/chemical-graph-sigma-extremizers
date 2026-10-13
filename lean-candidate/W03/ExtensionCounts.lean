import W03.FourVertexExtension
import Lean.Elab.Tactic.Omega

namespace W03

open scoped Classical

/-- The number of vertices having degree d, using the actual finite neighborhood. -/
noncomputable def degreeMultiplicity {V : Type*} [Fintype V]
    (G : SimpleGraph V) (d : ℕ) : ℕ :=
  (Finset.univ.filter fun x => vertexDegree G x = d).card

theorem extend4_degreeMultiplicity_split {V : Type*} [Fintype V]
    (G : SimpleGraph V) (u v : V) (huv : G.Adj u v) (d : ℕ) :
    degreeMultiplicity (extend4 G u v) d = degreeMultiplicity G d +
      ((Finset.univ : Finset (Fin 4)).filter fun i => i.val + 1 = d).card := by
  classical
  have hset :
      (Finset.univ.filter fun z => vertexDegree (extend4 G u v) z = d) =
      (Finset.univ.filter fun x => vertexDegree G x = d).disjSum
        ((Finset.univ : Finset (Fin 4)).filter fun i => i.val + 1 = d) := by
    ext z
    rcases z with x | i
    · simp [extend4_degree_inl G u v huv]
    · simp [extend4_degree_inr G u v]
  unfold degreeMultiplicity
  rw [hset, Finset.card_disjSum]

theorem extend4_degreeMultiplicity {V : Type*} [Fintype V]
    (G : SimpleGraph V) (u v : V) (huv : G.Adj u v) (i : Fin 4) :
    degreeMultiplicity (extend4 G u v) (i.val + 1) =
      degreeMultiplicity G (i.val + 1) + 1 := by
  have hcard : ((Finset.univ : Finset (Fin 4)).filter
      fun j => j.val + 1 = i.val + 1).card = 1 := by
    fin_cases i <;> decide
  rw [extend4_degreeMultiplicity_split G u v huv, hcard]

theorem extend4_maxDegree {V : Type*} [Fintype V]
    (G : SimpleGraph V) (u v : V) (huv : G.Adj u v)
    (hmax : ∀ x, vertexDegree G x ≤ 4) :
    ∀ z, vertexDegree (extend4 G u v) z ≤ 4 := by
  rintro (x | i)
  · rw [extend4_degree_inl G u v huv]
    exact hmax x
  · rw [extend4_degree_inr]
    have hi := i.isLt
    omega

end W03

set_option pp.all true
#print W03.degreeMultiplicity
#check @W03.degreeMultiplicity
#print axioms W03.degreeMultiplicity
#check @W03.extend4_degreeMultiplicity_split
#print axioms W03.extend4_degreeMultiplicity_split
#check @W03.extend4_degreeMultiplicity
#print axioms W03.extend4_degreeMultiplicity
#check @W03.extend4_maxDegree
#print axioms W03.extend4_maxDegree
