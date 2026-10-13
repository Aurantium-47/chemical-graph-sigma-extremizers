import W03.ProfileConstraints
import W03.TotalIndex

namespace W03

/-- The quadratic parity penalty, before any coefficient bounds are imposed. -/
def quadraticPenalty (T S u v : ℝ) : ℝ :=
  S * u ^ 2 + v ^ 2 + 2 * (T - 1) * u * v

theorem quadraticPenalty_three_squares (T S u v : ℝ) :
    quadraticPenalty T S u v =
      (S - T + 1) * u ^ 2 + (2 - T) * v ^ 2 + (T - 1) * (u + v) ^ 2 := by
  unfold quadraticPenalty
  ring

theorem indexQuadratic_decomposition {n : ℕ} (hn : 7 ≤ n)
    (G : SimpleGraph (Fin n)) (hc : G.Connected)
    (hmax : ∀ x, vertexDegree G x ≤ 4) :
    let T := Real.rpow 2 (1 / (n : ℝ))
    let S := Real.rpow 3 (1 / (n : ℝ))
    let s : ℝ := (degreeS G : ℝ)
    let u : ℝ := (degreeU G : ℝ)
    let v : ℝ := (degreeV G : ℝ)
    4 * indexQuadratic G =
      (n : ℝ) ^ 2 + 2 * (n : ℝ) * T * s - (1 + 2 * T - S) * s ^ 2 -
        quadraticPenalty T S u v := by
  have hsum := congrArg (fun k : ℕ => (k : ℝ))
    (chemical_multiplicities_sum hn G hc hmax)
  simp only [Nat.cast_add] at hsum
  dsimp only
  unfold indexQuadratic degreeS degreeU degreeV quadraticPenalty
  simp only [Int.cast_add, Int.cast_sub, Int.cast_natCast]
  rw [← hsum]
  ring

theorem totalIndex_decomposition {n : ℕ} (hn : 7 ≤ n)
    (G : SimpleGraph (Fin n)) (hc : G.Connected)
    (hmax : ∀ x, vertexDegree G x ≤ 4) :
    let T := Real.rpow 2 (1 / (n : ℝ))
    let S := Real.rpow 3 (1 / (n : ℝ))
    let s : ℝ := (degreeS G : ℝ)
    let u : ℝ := (degreeU G : ℝ)
    let v : ℝ := (degreeV G : ℝ)
    4 * totalIndex G =
      (n : ℝ) ^ 2 + 2 * (n : ℝ) * T * s - (1 + 2 * T - S) * s ^ 2 -
        quadraticPenalty T S u v := by
  dsimp only
  rw [totalIndex_eq_indexQuadratic hn G hc hmax]
  exact indexQuadratic_decomposition hn G hc hmax

end W03

set_option pp.all true
#print W03.quadraticPenalty
#check @W03.quadraticPenalty
#print axioms W03.quadraticPenalty
#check @W03.quadraticPenalty_three_squares
#print axioms W03.quadraticPenalty_three_squares
#check @W03.indexQuadratic_decomposition
#print axioms W03.indexQuadratic_decomposition
#check @W03.totalIndex_decomposition
#print axioms W03.totalIndex_decomposition
