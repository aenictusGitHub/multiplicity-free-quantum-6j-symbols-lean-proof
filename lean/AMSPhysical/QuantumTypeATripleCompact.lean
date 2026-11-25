import QuantumTypeAMixedTriple
import QuantumPhysicalTripleMetric

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def physicalTripleTensorBilin (q : ℝ) (n l m c : ℕ) :
    quantumOccupationTripleSpace n l m c →ₗ[ℝ] quantumOccupationTripleSpace n l m c →ₗ[ℝ] ℝ := by
  let V := quantumOccupationSpace ℝ (Fin (n+1)) l
  let W := quantumOccupationSpace ℝ (Fin (n+1)) m ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) c
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  letI : AddCommGroup W := inferInstance
  letI : Module ℝ W := inferInstance
  exact tensorWeightedBilin (V:=V) (W:=W) (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l)
        ((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m).tensorProduct
          (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) c))
        (occupationCompactWeight q n l)
        (fun yz : occupationWeights (Fin (n+1)) m × occupationWeights (Fin (n+1)) c =>occupationOppositeWeight q n m yz.1*occupationCompactWeight q n c yz.2)

theorem physicalTripleBilin_tensor (q : ℝ) (n l m c : ℕ) :
    physicalTripleBilin q n l m c=physicalTripleTensorBilin q n l m c := by
  have hw : physicalTripleWeight q n l m c=
      (fun p : OccupationTripleIndex n l m c =>occupationCompactWeight q n l p.1*
        (occupationOppositeWeight q n m p.2.1*occupationCompactWeight q n c p.2.2)) := by
    funext p
    unfold physicalTripleWeight
    ring
  unfold physicalTripleBilin physicalTripleTensorBilin tensorWeightedBilin
  rw [hw]
  rfl

theorem typeAMixedTriple_compact (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n l m c : ℕ) :
    IsCompactTypeAPair (V:=quantumOccupationTripleSpace n l m c) q n (physicalTripleBilin q n l m c)
      (typeAMixedTriple q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m c) := by
  let V := quantumOccupationSpace ℝ (Fin (n+1)) l
  let W := quantumOccupationSpace ℝ (Fin (n+1)) m ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) c
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  letI : AddCommGroup W := inferInstance
  letI : Module ℝ W := inferInstance
  rw [physicalTripleBilin_tensor]
  unfold physicalTripleTensorBilin typeAMixedTriple
  exact compactTypeAPair_tensor (V:=V) (W:=W) q (ne_of_gt hq) n
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l)
    ((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m).tensorProduct
      (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) c))
    (occupationCompactWeight q n l) (fun yz : occupationWeights (Fin (n+1)) m × occupationWeights (Fin (n+1)) c =>occupationOppositeWeight q n m yz.1*occupationCompactWeight q n c yz.2)
    (typeAFiniteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l)
    (typeAReverseMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n m c)
    (typeASymmetric_compact q hq hq1 n l) (typeAReverseMixedTensor_compact q hq hq1 n m c)

end AMSPhysical
#print axioms AMSPhysical.typeAMixedTriple_compact
