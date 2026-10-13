import W03.BaseGraphs

namespace W03

theorem base7_degrees (x : Fin 7) :
    vertexDegree base7 x = blockDegrees 2 1 2 x := by
  rw [vertexDegree_eq_degree]
  fin_cases x <;> decide

theorem base7_connected : base7.Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable base7).mpr
  refine ⟨6, ?_⟩
  intro x
  fin_cases x
  · exact (show base7.Adj 6 2 from by decide).reachable.trans ((show base7.Adj 2 0 from by decide).reachable)
  · exact (show base7.Adj 6 5 from by decide).reachable.trans ((show base7.Adj 5 1 from by decide).reachable)
  · exact (show base7.Adj 6 2 from by decide).reachable
  · exact (show base7.Adj 6 3 from by decide).reachable
  · exact (show base7.Adj 6 4 from by decide).reachable
  · exact (show base7.Adj 6 5 from by decide).reachable
  · exact SimpleGraph.Reachable.refl _

theorem base7_certificate : CertifiedBase base7 (profile4 2 1 2 2) 0 2 := by
  refine ⟨base7_connected, ?_, ?_, by decide⟩
  · intro x
    rw [base7_degrees]
    fin_cases x <;> decide
  · intro i
    rw [degreeMultiplicity_eq_card_filter base7 (blockDegrees 2 1 2) base7_degrees]
    fin_cases i <;> decide

theorem base8_degrees (x : Fin 8) :
    vertexDegree base8 x = blockDegrees 2 2 2 x := by
  rw [vertexDegree_eq_degree]
  fin_cases x <;> decide

theorem base8_connected : base8.Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable base8).mpr
  refine ⟨6, ?_⟩
  intro x
  fin_cases x
  · exact (show base8.Adj 6 2 from by decide).reachable.trans ((show base8.Adj 2 0 from by decide).reachable)
  · exact (show base8.Adj 6 7 from by decide).reachable.trans ((show base8.Adj 7 3 from by decide).reachable.trans ((show base8.Adj 3 1 from by decide).reachable))
  · exact (show base8.Adj 6 2 from by decide).reachable
  · exact (show base8.Adj 6 7 from by decide).reachable.trans ((show base8.Adj 7 3 from by decide).reachable)
  · exact (show base8.Adj 6 4 from by decide).reachable
  · exact (show base8.Adj 6 5 from by decide).reachable
  · exact SimpleGraph.Reachable.refl _
  · exact (show base8.Adj 6 7 from by decide).reachable

theorem base8_certificate : CertifiedBase base8 (profile4 2 2 2 2) 0 2 := by
  refine ⟨base8_connected, ?_, ?_, by decide⟩
  · intro x
    rw [base8_degrees]
    fin_cases x <;> decide
  · intro i
    rw [degreeMultiplicity_eq_card_filter base8 (blockDegrees 2 2 2) base8_degrees]
    fin_cases i <;> decide

theorem base9_degrees (x : Fin 9) :
    vertexDegree base9 x = blockDegrees 2 2 2 x := by
  rw [vertexDegree_eq_degree]
  fin_cases x <;> decide

theorem base9_connected : base9.Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable base9).mpr
  refine ⟨6, ?_⟩
  intro x
  fin_cases x
  · exact (show base9.Adj 6 2 from by decide).reachable.trans ((show base9.Adj 2 0 from by decide).reachable)
  · exact (show base9.Adj 6 3 from by decide).reachable.trans ((show base9.Adj 3 1 from by decide).reachable)
  · exact (show base9.Adj 6 2 from by decide).reachable
  · exact (show base9.Adj 6 3 from by decide).reachable
  · exact (show base9.Adj 6 7 from by decide).reachable.trans ((show base9.Adj 7 4 from by decide).reachable)
  · exact (show base9.Adj 6 7 from by decide).reachable.trans ((show base9.Adj 7 5 from by decide).reachable)
  · exact SimpleGraph.Reachable.refl _
  · exact (show base9.Adj 6 7 from by decide).reachable
  · exact (show base9.Adj 6 8 from by decide).reachable

theorem base9_certificate : CertifiedBase base9 (profile4 2 2 2 3) 0 2 := by
  refine ⟨base9_connected, ?_, ?_, by decide⟩
  · intro x
    rw [base9_degrees]
    fin_cases x <;> decide
  · intro i
    rw [degreeMultiplicity_eq_card_filter base9 (blockDegrees 2 2 2) base9_degrees]
    fin_cases i <;> decide

theorem base10A_degrees (x : Fin 10) :
    vertexDegree base10A x = blockDegrees 2 3 2 x := by
  rw [vertexDegree_eq_degree]
  fin_cases x <;> decide

theorem base10A_connected : base10A.Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable base10A).mpr
  refine ⟨8, ?_⟩
  intro x
  fin_cases x
  · exact (show base10A.Adj 8 6 from by decide).reachable.trans ((show base10A.Adj 6 2 from by decide).reachable.trans ((show base10A.Adj 2 0 from by decide).reachable))
  · exact (show base10A.Adj 8 5 from by decide).reachable.trans ((show base10A.Adj 5 1 from by decide).reachable)
  · exact (show base10A.Adj 8 6 from by decide).reachable.trans ((show base10A.Adj 6 2 from by decide).reachable)
  · exact (show base10A.Adj 8 7 from by decide).reachable.trans ((show base10A.Adj 7 3 from by decide).reachable)
  · exact (show base10A.Adj 8 7 from by decide).reachable.trans ((show base10A.Adj 7 4 from by decide).reachable)
  · exact (show base10A.Adj 8 5 from by decide).reachable
  · exact (show base10A.Adj 8 6 from by decide).reachable
  · exact (show base10A.Adj 8 7 from by decide).reachable
  · exact SimpleGraph.Reachable.refl _
  · exact (show base10A.Adj 8 9 from by decide).reachable

theorem base10A_certificate : CertifiedBase base10A (profile4 2 3 2 3) 0 2 := by
  refine ⟨base10A_connected, ?_, ?_, by decide⟩
  · intro x
    rw [base10A_degrees]
    fin_cases x <;> decide
  · intro i
    rw [degreeMultiplicity_eq_card_filter base10A (blockDegrees 2 3 2) base10A_degrees]
    fin_cases i <;> decide

theorem base10B_degrees (x : Fin 10) :
    vertexDegree base10B x = blockDegrees 3 2 3 x := by
  rw [vertexDegree_eq_degree]
  fin_cases x <;> decide

theorem base10B_connected : base10B.Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable base10B).mpr
  refine ⟨8, ?_⟩
  intro x
  fin_cases x
  · exact (show base10B.Adj 8 5 from by decide).reachable.trans ((show base10B.Adj 5 0 from by decide).reachable)
  · exact (show base10B.Adj 8 6 from by decide).reachable.trans ((show base10B.Adj 6 1 from by decide).reachable)
  · exact (show base10B.Adj 8 7 from by decide).reachable.trans ((show base10B.Adj 7 4 from by decide).reachable.trans ((show base10B.Adj 4 3 from by decide).reachable.trans ((show base10B.Adj 3 2 from by decide).reachable)))
  · exact (show base10B.Adj 8 7 from by decide).reachable.trans ((show base10B.Adj 7 4 from by decide).reachable.trans ((show base10B.Adj 4 3 from by decide).reachable))
  · exact (show base10B.Adj 8 7 from by decide).reachable.trans ((show base10B.Adj 7 4 from by decide).reachable)
  · exact (show base10B.Adj 8 5 from by decide).reachable
  · exact (show base10B.Adj 8 6 from by decide).reachable
  · exact (show base10B.Adj 8 7 from by decide).reachable
  · exact SimpleGraph.Reachable.refl _
  · exact (show base10B.Adj 8 9 from by decide).reachable

theorem base10B_certificate : CertifiedBase base10B (profile4 3 2 3 2) 0 5 := by
  refine ⟨base10B_connected, ?_, ?_, by decide⟩
  · intro x
    rw [base10B_degrees]
    fin_cases x <;> decide
  · intro i
    rw [degreeMultiplicity_eq_card_filter base10B (blockDegrees 3 2 3) base10B_degrees]
    fin_cases i <;> decide

theorem five_base_realizations :
    CertifiedBase base7 (profile4 2 1 2 2) 0 2 ∧
    CertifiedBase base8 (profile4 2 2 2 2) 0 2 ∧
    CertifiedBase base9 (profile4 2 2 2 3) 0 2 ∧
    CertifiedBase base10A (profile4 2 3 2 3) 0 2 ∧
    CertifiedBase base10B (profile4 3 2 3 2) 0 5 := by
  exact ⟨base7_certificate, base8_certificate, base9_certificate,
    base10A_certificate, base10B_certificate⟩

end W03

set_option pp.all true
#check @W03.base7_degrees
#print axioms W03.base7_degrees
#check @W03.base7_connected
#print axioms W03.base7_connected
#check @W03.base7_certificate
#print axioms W03.base7_certificate
#check @W03.base8_degrees
#print axioms W03.base8_degrees
#check @W03.base8_connected
#print axioms W03.base8_connected
#check @W03.base8_certificate
#print axioms W03.base8_certificate
#check @W03.base9_degrees
#print axioms W03.base9_degrees
#check @W03.base9_connected
#print axioms W03.base9_connected
#check @W03.base9_certificate
#print axioms W03.base9_certificate
#check @W03.base10A_degrees
#print axioms W03.base10A_degrees
#check @W03.base10A_connected
#print axioms W03.base10A_connected
#check @W03.base10A_certificate
#print axioms W03.base10A_certificate
#check @W03.base10B_degrees
#print axioms W03.base10B_degrees
#check @W03.base10B_connected
#print axioms W03.base10B_connected
#check @W03.base10B_certificate
#print axioms W03.base10B_certificate
#check @W03.five_base_realizations
#print axioms W03.five_base_realizations
