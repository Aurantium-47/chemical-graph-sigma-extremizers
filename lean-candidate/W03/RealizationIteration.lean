import W03.BaseCertificates

namespace W03

/-- A realization on the specified finite type, retaining an edge for extension. -/
def Realizes (n : ℕ) (p : Fin 4 → ℕ) : Prop :=
  ∃ G : SimpleGraph (Fin n), ∃ u v : Fin n, CertifiedBase G p u v

theorem profile4_add (a b c d t : ℕ) :
    (fun i => profile4 a b c d i + t) = profile4 (a + t) (b + t) (c + t) (d + t) := by
  funext i
  fin_cases i <;> rfl

theorem realizes_add_four {n : ℕ} {p : Fin 4 → ℕ} (h : Realizes n p) :
    Realizes (n + 4) (fun i => p i + 1) := by
  rcases h with ⟨G, u, v, hc⟩
  exact ⟨extend4Fin G u v, Fin.natAdd n 0, Fin.natAdd n 3,
    certifiedBase_extend G p u v hc⟩

theorem realizes_iterate {n : ℕ} {p : Fin 4 → ℕ} (h : Realizes n p) (t : ℕ) :
    Realizes (n + 4 * t) (fun i => p i + t) := by
  induction t with
  | zero => simpa only [Nat.mul_zero, Nat.add_zero] using h
  | succ t ih =>
    simpa only [Nat.mul_succ, Nat.add_assoc, Nat.succ_eq_add_one] using realizes_add_four ih

theorem realizes_profile4_iterate {n a b c d : ℕ}
    (h : Realizes n (profile4 a b c d)) (t : ℕ) :
    Realizes (n + 4 * t) (profile4 (a + t) (b + t) (c + t) (d + t)) := by
  simpa only [profile4_add] using realizes_iterate h t

end W03

set_option pp.all true
#print W03.Realizes
#check @W03.Realizes
#print axioms W03.Realizes
#check @W03.profile4_add
#print axioms W03.profile4_add
#check @W03.realizes_add_four
#print axioms W03.realizes_add_four
#check @W03.realizes_iterate
#print axioms W03.realizes_iterate
#check @W03.realizes_profile4_iterate
#print axioms W03.realizes_profile4_iterate
