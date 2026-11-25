import QuantumTypeIITriple

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 500000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem physicalTypeIITripleBilin_symm (q : ℝ) (n a b c : ℕ) (v w:quantumOccupationTripleSpace n a b c) :
    physicalTypeIITripleBilin q n a b c v w=physicalTypeIITripleBilin q n a b c w v := by
  exact finiteWeightedPair_symm _ _ v w

theorem typeATypeIITriple_compact (q : ℝ) (hq:0<q) (hq1:q≠1) (n a b c:ℕ) :
    IsCompactTypeAPair q n (physicalTypeIITripleBilin q n a b c)
      (typeATypeIITriple q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c) := by
  let V:=quantumOccupationSpace ℝ (Fin (n+1)) a
  let W:=quantumOccupationSpace ℝ (Fin (n+1)) b ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) c
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  letI : AddCommGroup W := inferInstance
  letI : Module ℝ W := inferInstance
  exact compactTypeAPair_tensor (V:=V) (W:=W) q (ne_of_gt hq) n
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) a)
    ((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) b).tensorProduct
      (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) c))
    (occupationCompactWeight q n a) (fun yz=>occupationCompactWeight q n b yz.1*occupationOppositeWeight q n c yz.2)
    (typeAFiniteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a)
    (typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n b c)
    (typeASymmetric_compact q hq hq1 n a) (typeAMixedTensor_compact q hq hq1 n b c)

end AMSPhysical
#print axioms AMSPhysical.typeATypeIITriple_compact
