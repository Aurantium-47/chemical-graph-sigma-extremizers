import W03.ExtensionCounts
import W03.FourVertexExtensionConnected
import Mathlib.Logic.Equiv.Fin.Basic

namespace W03

open SimpleGraph
open scoped Classical

theorem iso_vertexDegree {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) (x : V) :
    vertexDegree H (e x) = vertexDegree G x := by
  classical
  letI : Fintype (G.neighborSet x) := Fintype.ofFinite _
  letI : Fintype (H.neighborSet (e x)) := Fintype.ofFinite _
  calc
    vertexDegree H (e x) = Fintype.card (H.neighborSet (e x)) := by
      rw [vertexDegree_eq_degree, SimpleGraph.card_neighborSet_eq_degree]
    _ = Fintype.card (G.neighborSet x) := (Fintype.card_congr (e.mapNeighborSet x)).symm
    _ = vertexDegree G x := by
      rw [vertexDegree_eq_degree, SimpleGraph.card_neighborSet_eq_degree]

theorem iso_degreeMultiplicity {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) (d : ℕ) :
    degreeMultiplicity H d = degreeMultiplicity G d := by
  classical
  symm
  unfold degreeMultiplicity
  refine Finset.card_bij (fun x _ => e x) ?_ ?_ ?_
  · intro x hx
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, iso_vertexDegree e x] using hx
  · intro x hx y hy heq
    exact e.toEquiv.injective heq
  · intro y hy
    refine ⟨e.symm y, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    have hdeg : vertexDegree H y = vertexDegree G (e.symm y) := by
      simpa using iso_vertexDegree e (e.symm y)
    exact hdeg.symm.trans hy

/-- Relabel the explicit extension through Fin n + Fin 4 equiv Fin (n+4). -/
def extend4Fin {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    SimpleGraph (Fin (n + 4)) :=
  (extend4 G u v).map (finSumFinEquiv : Fin n ⊕ Fin 4 ≃ Fin (n + 4)).toEmbedding

/-- The actual graph isomorphism used for the relabeling. -/
def extend4FinIso {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    extend4 G u v ≃g extend4Fin G u v :=
  SimpleGraph.Iso.map finSumFinEquiv (extend4 G u v)

theorem extend4Fin_degree {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n)
    (z : Fin n ⊕ Fin 4) :
    vertexDegree (extend4Fin G u v) (finSumFinEquiv z) =
      vertexDegree (extend4 G u v) z :=
  iso_vertexDegree (extend4FinIso G u v) z

theorem extend4Fin_markedEdge {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    (extend4Fin G u v).Adj (Fin.natAdd n 0) (Fin.natAdd n 3) := by
  have h := (extend4FinIso G u v).map_adj_iff.mpr (extend4_markedEdge G u v)
  simpa [extend4FinIso] using h

/-- An explicit output graph and marked edge ready for another extension. -/
theorem extend4Fin_iterate {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n)
    (huv : G.Adj u v) (hG : G.Connected) (hmax : ∀ x, vertexDegree G x ≤ 4) :
    let H := extend4Fin G u v
    H.Connected ∧
    (∀ x, vertexDegree H x ≤ 4) ∧
    (∀ i : Fin 4, degreeMultiplicity H (i.val + 1) = degreeMultiplicity G (i.val + 1) + 1) ∧
    (∀ x : Fin n, vertexDegree H (Fin.castAdd 4 x) = vertexDegree G x) ∧
    (∀ i : Fin 4, vertexDegree H (Fin.natAdd n i) = i.val + 1) ∧
    H.Adj (Fin.natAdd n 0) (Fin.natAdd n 3) := by
  dsimp only
  refine ⟨(extend4FinIso G u v).connected_iff.mp (extend4_connected G u v hG),
    ?_, ?_, ?_, ?_, extend4Fin_markedEdge G u v⟩
  · intro x
    rcases (finSumFinEquiv : Fin n ⊕ Fin 4 ≃ Fin (n + 4)).surjective x with ⟨z, rfl⟩
    rw [extend4Fin_degree]
    exact extend4_maxDegree G u v huv hmax z
  · intro i
    exact (iso_degreeMultiplicity (extend4FinIso G u v) (i.val + 1)).trans
      (extend4_degreeMultiplicity G u v huv i)
  · intro x
    simpa using (extend4Fin_degree G u v (Sum.inl x)).trans (extend4_degree_inl G u v huv x)
  · intro i
    simpa using (extend4Fin_degree G u v (Sum.inr i)).trans (extend4_degree_inr G u v i)

end W03

set_option pp.all true
#print W03.extend4Fin
#print W03.extend4FinIso
#check @W03.iso_vertexDegree
#print axioms W03.iso_vertexDegree
#check @W03.iso_degreeMultiplicity
#print axioms W03.iso_degreeMultiplicity
#check @W03.extend4Fin
#print axioms W03.extend4Fin
#check @W03.extend4FinIso
#print axioms W03.extend4FinIso
#check @W03.extend4Fin_degree
#print axioms W03.extend4Fin_degree
#check @W03.extend4Fin_markedEdge
#print axioms W03.extend4Fin_markedEdge
#check @W03.extend4Fin_iterate
#print axioms W03.extend4Fin_iterate
