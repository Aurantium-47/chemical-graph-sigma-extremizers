import W03.FiniteExtension

namespace W03

/-- A finite edge list, symmetrized with loops excluded. -/
def edgeGraph {n : ℕ} (edges : Finset (Fin n × Fin n)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun x y => (x, y) ∈ edges

instance edgeGraphDecidable {n : ℕ} (edges : Finset (Fin n × Fin n)) :
    DecidableRel (edgeGraph edges).Adj := fun x y =>
  inferInstanceAs (Decidable (x ≠ y ∧ ((x, y) ∈ edges ∨ (y, x) ∈ edges)))

/-- Four multiplicities, indexed by degree minus one. -/
def profile4 (a b c d : ℕ) (i : Fin 4) : ℕ :=
  match i.val with
  | 0 => a
  | 1 => b
  | 2 => c
  | _ => d

/-- A degree vector with consecutive blocks of degrees 1, 2, 3 and 4. -/
def blockDegrees {n : ℕ} (a b c : ℕ) (x : Fin n) : ℕ :=
  if x.val < a then 1 else if x.val < a + b then 2
  else if x.val < a + b + c then 3 else 4

theorem degreeMultiplicity_eq_card_filter {V : Type*} [Fintype V]
    (G : SimpleGraph V) (f : V → ℕ) (hf : ∀ x, vertexDegree G x = f x) (d : ℕ) :
    degreeMultiplicity G d = (Finset.univ.filter fun x => f x = d).card := by
  classical
  unfold degreeMultiplicity
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hf]

/-- All properties needed to start the four-vertex extension. -/
def CertifiedBase {n : ℕ} (G : SimpleGraph (Fin n)) (p : Fin 4 → ℕ) (u v : Fin n) : Prop :=
  G.Connected ∧ (∀ x, vertexDegree G x ≤ 4) ∧
    (∀ i : Fin 4, degreeMultiplicity G (i.val + 1) = p i) ∧ G.Adj u v

theorem certifiedBase_extend {n : ℕ} (G : SimpleGraph (Fin n))
    (p : Fin 4 → ℕ) (u v : Fin n) (h : CertifiedBase G p u v) :
    CertifiedBase (extend4Fin G u v) (fun i => p i + 1)
      (Fin.natAdd n 0) (Fin.natAdd n 3) := by
  have hnext := extend4Fin_iterate G u v h.2.2.2 h.1 h.2.1
  refine ⟨hnext.1, hnext.2.1, ?_, hnext.2.2.2.2.2⟩
  intro i
  exact (hnext.2.2.1 i).trans (congrArg (fun a : ℕ => a + 1) (h.2.2.1 i))

abbrev base7 : SimpleGraph (Fin 7) :=
  edgeGraph {(0, 2), (1, 5), (2, 6), (3, 4), (3, 5), (3, 6), (4, 5), (4, 6), (5, 6)}

abbrev base8 : SimpleGraph (Fin 8) :=
  edgeGraph {(0, 2), (1, 3), (2, 6), (3, 7), (4, 5), (4, 6), (4, 7), (5, 6), (5, 7), (6, 7)}

abbrev base9 : SimpleGraph (Fin 9) :=
  edgeGraph {(0, 2), (1, 3), (2, 6), (3, 6), (4, 5), (4, 7), (4, 8), (5, 7), (5, 8), (6, 7), (6, 8), (7, 8)}

abbrev base10A : SimpleGraph (Fin 10) :=
  edgeGraph {(0, 2), (1, 5), (2, 6), (3, 4), (3, 7), (4, 7), (5, 8), (5, 9), (6, 8), (6, 9), (7, 8), (7, 9), (8, 9)}

abbrev base10B : SimpleGraph (Fin 10) :=
  edgeGraph {(0, 5), (1, 6), (2, 3), (3, 4), (4, 7), (5, 8), (5, 9), (6, 8), (6, 9), (7, 8), (7, 9), (8, 9)}

end W03

set_option pp.all true
#print W03.edgeGraph
#print W03.edgeGraphDecidable
#print W03.profile4
#print W03.blockDegrees
#print W03.CertifiedBase
#print W03.base7
#print W03.base8
#print W03.base9
#print W03.base10A
#print W03.base10B
#check @W03.edgeGraph
#print axioms W03.edgeGraph
#check @W03.edgeGraphDecidable
#print axioms W03.edgeGraphDecidable
#check @W03.profile4
#print axioms W03.profile4
#check @W03.blockDegrees
#print axioms W03.blockDegrees
#check @W03.degreeMultiplicity_eq_card_filter
#print axioms W03.degreeMultiplicity_eq_card_filter
#check @W03.CertifiedBase
#print axioms W03.CertifiedBase
#check @W03.certifiedBase_extend
#print axioms W03.certifiedBase_extend
#check @W03.base7
#print axioms W03.base7
#check @W03.base8
#print axioms W03.base8
#check @W03.base9
#print axioms W03.base9
#check @W03.base10A
#print axioms W03.base10A
#check @W03.base10B
#print axioms W03.base10B
