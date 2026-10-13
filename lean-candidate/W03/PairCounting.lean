import W03.ExtensionCounts
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

namespace W03

open scoped BigOperators Classical

theorem connected_vertexDegree_pos {n : ℕ} (hn : 2 ≤ n)
    (G : SimpleGraph (Fin n)) (hc : G.Connected) (x : Fin n) :
    0 < vertexDegree G x := by
  classical
  have hex : ∃ y : Fin n, x ≠ y := by
    by_cases hx : x.val = 0
    · refine ⟨⟨1, by omega⟩, ?_⟩
      intro heq
      have hval := congrArg Fin.val heq
      simp only at hval
      omega
    · refine ⟨⟨0, by omega⟩, ?_⟩
      intro heq
      exact hx (congrArg Fin.val heq)
  obtain ⟨y, hxy⟩ := hex
  obtain ⟨p⟩ := hc.preconnected x y
  exact Finset.card_pos.mpr ⟨p.snd, (mem_neighbors G x p.snd).mpr
    (SimpleGraph.Walk.adj_snd (p := p) (SimpleGraph.Walk.not_nil_of_ne hxy))⟩

theorem sum_degree_classes {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hpos : ∀ x, 0 < vertexDegree G x)
    (hmax : ∀ x, vertexDegree G x ≤ 4) (f : ℕ → ℝ) :
    (∑ x, f (vertexDegree G x)) =
      (degreeMultiplicity G 1 : ℝ) * f 1 +
      (degreeMultiplicity G 2 : ℝ) * f 2 +
      (degreeMultiplicity G 3 : ℝ) * f 3 +
      (degreeMultiplicity G 4 : ℝ) * f 4 := by
  classical
  have hm : ∀ x ∈ (Finset.univ : Finset V),
      vertexDegree G x ∈ ({1, 2, 3, 4} : Finset ℕ) := by
    intro x _
    have hp := hpos x
    have hu := hmax x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have hs := Finset.sum_fiberwise_of_maps_to'
    (s := Finset.univ) (t := {1, 2, 3, 4}) (g := vertexDegree G) hm f
  simpa [degreeMultiplicity, nsmul_eq_mul, add_assoc] using hs.symm

theorem ordered_sum_eq_twice_unordered {n : ℕ} (f : Fin n → Fin n → ℝ)
    (hsym : ∀ x y, f x y = f y x) (hdiag : ∀ x, f x x = 0) :
    (∑ x, ∑ y, f x y) =
      2 * (∑ x, ∑ y, if x < y then f x y else 0) := by
  have hp : ∀ x y, (if x < y then f x y else 0) +
      (if y < x then f y x else 0) = f x y := by
    intro x y
    rcases lt_trichotomy x y with h | h | h
    · simp [h, not_lt_of_gt h]
    · subst y
      simp [hdiag]
    · simp [h, not_lt_of_gt h, hsym]
  have hswap : (∑ x, ∑ y, if y < x then f y x else 0) =
      (∑ x, ∑ y, if x < y then f x y else 0) := Finset.sum_comm
  calc
    (∑ x, ∑ y, f x y) = ∑ x, ∑ y,
        ((if x < y then f x y else 0) +
          (if y < x then f y x else 0)) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      exact (hp x y).symm
    _ = (∑ x, ∑ y, if x < y then f x y else 0) +
        (∑ x, ∑ y, if y < x then f y x else 0) := by
      simp only [Finset.sum_add_distrib]
    _ = 2 * (∑ x, ∑ y, if x < y then f x y else 0) := by
      rw [hswap]
      ring

/-- The six distinct degree-class products, with each unordered class pair once. -/
noncomputable def pairQuadratic {V : Type*} [Fintype V]
    (G : SimpleGraph V) (w : ℕ → ℕ → ℝ) : ℝ :=
  (degreeMultiplicity G 1 : ℝ) * degreeMultiplicity G 2 * w 1 2 +
  (degreeMultiplicity G 1 : ℝ) * degreeMultiplicity G 3 * w 1 3 +
  (degreeMultiplicity G 1 : ℝ) * degreeMultiplicity G 4 * w 1 4 +
  (degreeMultiplicity G 2 : ℝ) * degreeMultiplicity G 3 * w 2 3 +
  (degreeMultiplicity G 2 : ℝ) * degreeMultiplicity G 4 * w 2 4 +
  (degreeMultiplicity G 3 : ℝ) * degreeMultiplicity G 4 * w 3 4

theorem ordered_degree_sum_eq_twice_quadratic {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hpos : ∀ x, 0 < vertexDegree G x)
    (hmax : ∀ x, vertexDegree G x ≤ 4) (w : ℕ → ℕ → ℝ)
    (hsym : ∀ d e, w d e = w e d) (hdiag : ∀ d, w d d = 0) :
    (∑ x, ∑ y, w (vertexDegree G x) (vertexDegree G y)) =
      2 * pairQuadratic G w := by
  rw [sum_degree_classes G hpos hmax
    (fun d => ∑ y, w d (vertexDegree G y)),
    sum_degree_classes G hpos hmax (w 1),
    sum_degree_classes G hpos hmax (w 2),
    sum_degree_classes G hpos hmax (w 3),
    sum_degree_classes G hpos hmax (w 4)]
  simp only [hdiag,
    hsym 2 1, hsym 3 1, hsym 4 1, hsym 3 2, hsym 4 2, hsym 4 3]
  unfold pairQuadratic
  ring

theorem chemical_unordered_degree_sum {n : ℕ} (hn : 7 ≤ n)
    (G : SimpleGraph (Fin n)) (hc : G.Connected)
    (hmax : ∀ x, vertexDegree G x ≤ 4) (w : ℕ → ℕ → ℝ)
    (hsym : ∀ d e, w d e = w e d) (hdiag : ∀ d, w d d = 0) :
    (∑ x, ∑ y, if x < y then
      w (vertexDegree G x) (vertexDegree G y) else 0) =
      pairQuadratic G w := by
  have hp := connected_vertexDegree_pos (by omega : 2 ≤ n) G hc
  have hu := ordered_sum_eq_twice_unordered
    (fun x y => w (vertexDegree G x) (vertexDegree G y))
    (fun x y => hsym _ _) (fun x => hdiag _)
  have hq := ordered_degree_sum_eq_twice_quadratic G hp hmax w hsym hdiag
  have hh := hu.symm.trans hq
  exact mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0) hh

end W03

set_option pp.all true
#check @W03.connected_vertexDegree_pos
#print axioms W03.connected_vertexDegree_pos
#check @W03.sum_degree_classes
#print axioms W03.sum_degree_classes
#check @W03.ordered_sum_eq_twice_unordered
#print axioms W03.ordered_sum_eq_twice_unordered
#print W03.pairQuadratic
#check @W03.pairQuadratic
#print axioms W03.pairQuadratic
#check @W03.ordered_degree_sum_eq_twice_quadratic
#print axioms W03.ordered_degree_sum_eq_twice_quadratic
#check @W03.chemical_unordered_degree_sum
#print axioms W03.chemical_unordered_degree_sum
