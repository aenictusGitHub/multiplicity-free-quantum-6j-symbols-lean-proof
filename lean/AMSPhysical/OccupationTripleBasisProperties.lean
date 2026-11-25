import OccupationTripleCoefficients

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical

theorem occupationTripleCoefficients_basis (n l m c : ℕ) (p : OccupationTripleIndex n l m c) :
    occupationTripleCoefficients n l m c (occupationTripleBasis n l m c p)=
      Finsupp.single (occupationTripleEmbedding n l m c p) 1 := by
  let V := quantumOccupationTripleSpace n l m c
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  exact injectedBasisCoefficients_basis (V:=V) (occupationTripleBasis n l m c) (occupationTripleEmbedding n l m c) p

theorem occupationTripleCoefficients_support (n l m c : ℕ) (v : quantumOccupationTripleSpace n l m c)
    (p : OccupationTripleLattice n) (hp : occupationTripleCoefficients n l m c v p≠0) :
    p.1∈occupationWeights (Fin (n+1)) l ∧ p.2.1∈occupationWeights (Fin (n+1)) m ∧
      p.2.2∈occupationWeights (Fin (n+1)) c := by
  let V := quantumOccupationTripleSpace n l m c
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  obtain ⟨i,hi⟩:=injectedBasisCoefficients_support (V:=V) (occupationTripleBasis n l m c)
    (occupationTripleEmbedding n l m c) v p hp
  rw [← hi]
  exact ⟨i.1.property,i.2.1.property,i.2.2.property⟩

end AMSPhysical
