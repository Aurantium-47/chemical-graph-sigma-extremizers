import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

namespace W03

open SimpleGraph
open scoped Classical

/-- The finite set of all vertices adjacent to a given vertex. -/
noncomputable def neighbors {V : Type*} [Fintype V]
    (G : SimpleGraph V) (x : V) : Finset V := by
  classical
  exact Finset.univ.filter (G.Adj x)

@[simp] theorem mem_neighbors {V : Type*} [Fintype V]
    (G : SimpleGraph V) (x y : V) : y ∈ neighbors G x ↔ G.Adj x y := by
  classical
  simp [neighbors]

/-- Degree, counted by the finite neighborhood. -/
noncomputable def vertexDegree {V : Type*} [Fintype V]
    (G : SimpleGraph V) (x : V) : ℕ := (neighbors G x).card

theorem vertexDegree_eq_degree {V : Type*} [Fintype V]
    (G : SimpleGraph V) (x : V) [Fintype (G.neighborSet x)] :
    vertexDegree G x = G.degree x := by
  classical
  have h : neighbors G x = G.neighborFinset x := by ext y; simp
  exact congrArg Finset.card h

/-- Four new vertices with edges 03, 12, 13 and 23. -/
def core4 : SimpleGraph (Fin 4) where
  Adj i j := (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) ∨
    (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) ∨
    (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1) ∨
    (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2)
  symm := by intro i j h; aesop
  loopless := by intro i; fin_cases i <;> decide

/-- Delete uv and attach the four-vertex core along u2 and v3. -/
def extend4 {V : Type*} (G : SimpleGraph V) (u v : V) :
    SimpleGraph (V ⊕ Fin 4) where
  Adj
    | Sum.inl a, Sum.inl b => G.Adj a b ∧ ¬ (a = u ∧ b = v) ∧ ¬ (a = v ∧ b = u)
    | Sum.inl a, Sum.inr i => (a = u ∧ i = 2) ∨ (a = v ∧ i = 3)
    | Sum.inr i, Sum.inl a => (a = u ∧ i = 2) ∨ (a = v ∧ i = 3)
    | Sum.inr i, Sum.inr j => core4.Adj i j
  symm := by
    rintro (a | i) (b | j) h
    · exact ⟨h.1.symm, by aesop, by aesop⟩
    · exact h
    · exact h
    · exact h.symm
  loopless := by
    rintro (a | i) h
    · exact G.loopless a h.1
    · exact core4.loopless i h

theorem neighbors_inl_u {V : Type*} [Fintype V]
    (G : SimpleGraph V) (u v : V) (huv : G.Adj u v) :
    neighbors (extend4 G u v) (Sum.inl u) =
      insert (Sum.inr 2) ((neighbors G u).erase v |>.map Function.Embedding.inl) := by
  classical
  ext y
  rcases y with y | i
  · simp [extend4, huv.ne, Ne.symm huv.ne, Function.Embedding.inl, and_comm]
  · simp [extend4, huv.ne, Ne.symm huv.ne, Function.Embedding.inl, eq_comm]

theorem neighbors_inl_v {V : Type*} [Fintype V]
    (G : SimpleGraph V) (u v : V) (huv : G.Adj u v) :
    neighbors (extend4 G u v) (Sum.inl v) =
      insert (Sum.inr 3) ((neighbors G v).erase u |>.map Function.Embedding.inl) := by
  classical
  ext y
  rcases y with y | i
  · simp [extend4, huv.ne, Ne.symm huv.ne, Function.Embedding.inl, and_comm]
  · simp [extend4, huv.ne, Ne.symm huv.ne, Function.Embedding.inl, eq_comm]

theorem neighbors_inl_other {V : Type*} [Fintype V]
    (G : SimpleGraph V) (u v x : V) (hxu : x ≠ u) (hxv : x ≠ v) :
    neighbors (extend4 G u v) (Sum.inl x) =
      (neighbors G x).map Function.Embedding.inl := by
  classical
  ext y
  rcases y with y | i <;> simp [extend4, hxu, hxv, Function.Embedding.inl]

theorem extend4_degree_inl {V : Type*} [Fintype V]
    (G : SimpleGraph V) (u v : V) (huv : G.Adj u v) (x : V) :
    vertexDegree (extend4 G u v) (Sum.inl x) = vertexDegree G x := by
  classical
  by_cases hxu : x = u
  · subst x
    have hv : v ∈ neighbors G u := (mem_neighbors G u v).2 huv
    have hp := Finset.card_pos.mpr ⟨v, hv⟩
    simp only [vertexDegree, neighbors_inl_u G u v huv]
    simp [Finset.card_erase_of_mem hv, Function.Embedding.inl] <;> omega
  · by_cases hxv : x = v
    · subst x
      have hu : u ∈ neighbors G v := (mem_neighbors G v u).2 huv.symm
      have hp := Finset.card_pos.mpr ⟨u, hu⟩
      simp only [vertexDegree, neighbors_inl_v G u v huv]
      simp [Finset.card_erase_of_mem hu, Function.Embedding.inl] <;> omega
    · simp [vertexDegree, neighbors_inl_other G u v x hxu hxv]

theorem neighbors_inr_zero {V : Type*} [Fintype V]
    (G : SimpleGraph V) (u v : V) :
    neighbors (extend4 G u v) (Sum.inr 0) = {Sum.inr 3} := by
  classical
  ext y
  rcases y with y | i
  · simp [extend4]
  · simp [extend4, core4, eq_comm]

theorem neighbors_inr_one {V : Type*} [Fintype V]
    (G : SimpleGraph V) (u v : V) :
    neighbors (extend4 G u v) (Sum.inr 1) = {Sum.inr 2, Sum.inr 3} := by
  classical
  ext y
  rcases y with y | i
  · simp [extend4]
  · simp [extend4, core4, eq_comm]

theorem neighbors_inr_two {V : Type*} [Fintype V]
    (G : SimpleGraph V) (u v : V) :
    neighbors (extend4 G u v) (Sum.inr 2) = {Sum.inl u, Sum.inr 1, Sum.inr 3} := by
  classical
  ext y
  rcases y with y | i
  · simp [extend4]
  · simp [extend4, core4, eq_comm]

theorem neighbors_inr_three {V : Type*} [Fintype V]
    (G : SimpleGraph V) (u v : V) :
    neighbors (extend4 G u v) (Sum.inr 3) =
      {Sum.inl v, Sum.inr 0, Sum.inr 1, Sum.inr 2} := by
  classical
  ext y
  rcases y with y | i
  · simp [extend4]
  · simp [extend4, core4, eq_comm]

theorem extend4_degree_inr {V : Type*} [Fintype V]
    (G : SimpleGraph V) (u v : V) (i : Fin 4) :
    vertexDegree (extend4 G u v) (Sum.inr i) = i.val + 1 := by
  classical
  fin_cases i <;> simp [vertexDegree, neighbors_inr_zero, neighbors_inr_one,
    neighbors_inr_two, neighbors_inr_three]

theorem extend4_markedEdge {V : Type*} (G : SimpleGraph V) (u v : V) :
    (extend4 G u v).Adj (Sum.inr 0) (Sum.inr 3) := by
  simp [extend4, core4]

end W03

set_option pp.all true
#print W03.neighbors
#print W03.vertexDegree
#print W03.core4
#print W03.extend4
#check @W03.neighbors
#print axioms W03.neighbors
#check @W03.mem_neighbors
#print axioms W03.mem_neighbors
#check @W03.vertexDegree
#print axioms W03.vertexDegree
#check @W03.vertexDegree_eq_degree
#print axioms W03.vertexDegree_eq_degree
#check @W03.core4
#print axioms W03.core4
#check @W03.extend4
#print axioms W03.extend4
#check @W03.neighbors_inl_u
#print axioms W03.neighbors_inl_u
#check @W03.neighbors_inl_v
#print axioms W03.neighbors_inl_v
#check @W03.neighbors_inl_other
#print axioms W03.neighbors_inl_other
#check @W03.extend4_degree_inl
#print axioms W03.extend4_degree_inl
#check @W03.neighbors_inr_zero
#print axioms W03.neighbors_inr_zero
#check @W03.neighbors_inr_one
#print axioms W03.neighbors_inr_one
#check @W03.neighbors_inr_two
#print axioms W03.neighbors_inr_two
#check @W03.neighbors_inr_three
#print axioms W03.neighbors_inr_three
#check @W03.extend4_degree_inr
#print axioms W03.extend4_degree_inr
#check @W03.extend4_markedEdge
#print axioms W03.extend4_markedEdge
