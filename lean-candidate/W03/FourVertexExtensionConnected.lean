import W03.FourVertexExtension
import Mathlib.Combinatorics.SimpleGraph.Path

namespace W03

open SimpleGraph
open scoped Classical

theorem extend4_reachable_uv {V : Type*} (G : SimpleGraph V) (u v : V) :
    (extend4 G u v).Reachable (Sum.inl u) (Sum.inl v) := by
  have h1 : (extend4 G u v).Adj (Sum.inl u) (Sum.inr 2) := by simp [extend4]
  have h2 : (extend4 G u v).Adj (Sum.inr 2) (Sum.inr 3) := by simp [extend4, core4]
  have h3 : (extend4 G u v).Adj (Sum.inr 3) (Sum.inl v) := by simp [extend4]
  exact h1.reachable.trans (h2.reachable.trans h3.reachable)

theorem extend4_reachable_of_adj {V : Type*} (G : SimpleGraph V) (u v : V)
    {a b : V} (hab : G.Adj a b) :
    (extend4 G u v).Reachable (Sum.inl a) (Sum.inl b) := by
  by_cases h : a = u ∧ b = v
  · rcases h with ⟨rfl, rfl⟩
    exact extend4_reachable_uv G u v
  · by_cases h' : a = v ∧ b = u
    · rcases h' with ⟨rfl, rfl⟩
      exact (extend4_reachable_uv G u v).symm
    · exact (show (extend4 G u v).Adj (Sum.inl a) (Sum.inl b) from
        ⟨hab, h, h'⟩).reachable

theorem extend4_reachable_old {V : Type*} (G : SimpleGraph V) (u v : V)
    {a b : V} (h : G.Reachable a b) :
    (extend4 G u v).Reachable (Sum.inl a) (Sum.inl b) := by
  rcases h with ⟨p⟩
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hab p ih => exact (extend4_reachable_of_adj G u v hab).trans ih

theorem extend4_reachable_new {V : Type*} (G : SimpleGraph V) (u v : V)
    (i : Fin 4) : (extend4 G u v).Reachable (Sum.inl u) (Sum.inr i) := by
  have h2 : (extend4 G u v).Reachable (Sum.inl u) (Sum.inr 2) :=
    (show (extend4 G u v).Adj (Sum.inl u) (Sum.inr 2) by simp [extend4]).reachable
  have h3 : (extend4 G u v).Reachable (Sum.inl u) (Sum.inr 3) :=
    h2.trans (show (extend4 G u v).Adj (Sum.inr 2) (Sum.inr 3) by
      simp [extend4, core4]).reachable
  fin_cases i
  · exact h3.trans (extend4_markedEdge G u v).symm.reachable
  · exact h2.trans (show (extend4 G u v).Adj (Sum.inr 2) (Sum.inr 1) by
      simp [extend4, core4]).reachable
  · exact h2
  · exact h3

theorem extend4_connected {V : Type*} (G : SimpleGraph V) (u v : V)
    (hG : G.Connected) : (extend4 G u v).Connected := by
  apply SimpleGraph.connected_iff_exists_forall_reachable.mpr
  refine ⟨Sum.inl u, ?_⟩
  rintro (x | i)
  · exact extend4_reachable_old G u v (hG u x)
  · exact extend4_reachable_new G u v i

/-- The same explicit graph has all degree, size and connectivity properties. -/
theorem extend4_bridge {V : Type*} [Fintype V]
    (G : SimpleGraph V) (u v : V) (huv : G.Adj u v) :
    let H := extend4 G u v
    Fintype.card (V ⊕ Fin 4) = Fintype.card V + 4 ∧
    (∀ x : V, vertexDegree H (Sum.inl x) = vertexDegree G x) ∧
    (∀ i : Fin 4, vertexDegree H (Sum.inr i) = i.val + 1) ∧
    H.Adj (Sum.inr 0) (Sum.inr 3) ∧
    (G.Connected → H.Connected) := by
  exact ⟨by simp, extend4_degree_inl G u v huv, extend4_degree_inr G u v,
    extend4_markedEdge G u v, extend4_connected G u v⟩

end W03

set_option pp.all true
#check @W03.extend4_reachable_uv
#print axioms W03.extend4_reachable_uv
#check @W03.extend4_reachable_of_adj
#print axioms W03.extend4_reachable_of_adj
#check @W03.extend4_reachable_old
#print axioms W03.extend4_reachable_old
#check @W03.extend4_reachable_new
#print axioms W03.extend4_reachable_new
#check @W03.extend4_connected
#print axioms W03.extend4_connected
#check @W03.extend4_bridge
#print axioms W03.extend4_bridge
