import W03.PairCounting
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace W03

open scoped BigOperators Classical

/-- Sum over all unordered distinct vertex pairs, using the vertex order once. -/
noncomputable def totalIndex {n : ℕ} (G : SimpleGraph (Fin n)) : ℝ :=
  ∑ x, ∑ y, if x < y then
    Real.rpow (|(vertexDegree G x : ℝ) - (vertexDegree G y : ℝ)|)
      (1 / (n : ℝ)) else 0

/-- The degree-multiplicity polynomial for exponent 1/n. -/
noncomputable def indexQuadratic {n : ℕ} (G : SimpleGraph (Fin n)) : ℝ :=
  (degreeMultiplicity G 1 : ℝ) * degreeMultiplicity G 2 +
  (degreeMultiplicity G 2 : ℝ) * degreeMultiplicity G 3 +
  (degreeMultiplicity G 3 : ℝ) * degreeMultiplicity G 4 +
  Real.rpow 2 (1 / (n : ℝ)) *
    ((degreeMultiplicity G 1 : ℝ) * degreeMultiplicity G 3 +
      (degreeMultiplicity G 2 : ℝ) * degreeMultiplicity G 4) +
  Real.rpow 3 (1 / (n : ℝ)) *
    (degreeMultiplicity G 1 : ℝ) * degreeMultiplicity G 4

theorem totalIndex_eq_indexQuadratic {n : ℕ} (hn : 7 ≤ n)
    (G : SimpleGraph (Fin n)) (hc : G.Connected)
    (hmax : ∀ x, vertexDegree G x ≤ 4) :
    totalIndex G = indexQuadratic G := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega : n ≠ 0)
  have hexp : (1 / (n : ℝ)) ≠ 0 := one_div_ne_zero hn0
  have hw := chemical_unordered_degree_sum hn G hc hmax
    (fun d e => Real.rpow (|(d : ℝ) - (e : ℝ)|) (1 / (n : ℝ)))
    (by
      intro d e
      exact congrArg (fun t : ℝ => Real.rpow t (1 / (n : ℝ)))
        (abs_sub_comm (d : ℝ) (e : ℝ)))
    (by
      intro d
      change Real.rpow (|(d : ℝ) - (d : ℝ)|) (1 / (n : ℝ)) = 0
      rw [sub_self, abs_zero]
      exact Real.zero_rpow hexp)
  change totalIndex G = _ at hw
  rw [hw]
  unfold pairQuadratic indexQuadratic
  norm_num
  ring

end W03

set_option pp.all true
#print W03.totalIndex
#check @W03.totalIndex
#print axioms W03.totalIndex
#print W03.indexQuadratic
#check @W03.indexQuadratic
#print axioms W03.indexQuadratic
#check @W03.totalIndex_eq_indexQuadratic
#print axioms W03.totalIndex_eq_indexQuadratic
