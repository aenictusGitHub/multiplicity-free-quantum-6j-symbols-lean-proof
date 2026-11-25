import QuantumMixedHomBending
import AlgebraIntertwinerTargetEquiv
import CompactHighestHomEquivalence
import QuantumSymmetricHighestRealization
import QuantumTypeATripleCompact

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def symmetricTripleHighestHomEquiv (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n L l m c : ℕ) :
    algebraIntertwinerSpace
      (V:=quantumOccupationSpace ℝ (Fin (n+1)) L) (W:=quantumOccupationTripleSpace n l m c)
      (typeAFiniteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L)
      (typeAMixedTriple q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m c) ≃ₗ[ℝ]
      typeAHighestSpace (V:=quantumOccupationTripleSpace n l m c) q n
        (typeAMixedTriple q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m c)
        (mixedHighestDynkin n L 0) := by
  let V := quantumOccupationSpace ℝ (Fin (n+1)) L
  let W := quantumOccupationTripleSpace n l m c
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  letI : AddCommGroup W := inferInstance
  letI : Module ℝ W := inferInstance
  exact compactHighestHomEquiv (V:=V) (W:=W) q (ne_of_gt hq) n (mixedHighestDynkin n L 0)
    (symmetricHighestRealization q hq hq1 n L) (symmetricHighestRealization_channel_top q hq hq1 n L)
    (typeAMixedTriple q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m c)
    (physicalTripleBilin q n l m c) (typeAMixedTriple_compact q hq hq1 n l m c)
    (physicalTripleBilin_symm q n l m c) (physicalTripleBilin_definite q hq n l m c)

/-- Actual pair-Hom/triple-Hom equivalence: invariant physical duality followed
by the proved quantum-group tensor associator. -/
def mixedPairTripleHomEquiv (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n a c l m : ℕ) :
    algebraIntertwinerSpace
      (V:=quantumOccupationSpace ℝ (Fin (n+1)) a ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) c)
      (W:=quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
      (typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a c)
      (typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m) ≃ₗ[ℝ]
      algebraIntertwinerSpace
        (V:=quantumOccupationSpace ℝ (Fin (n+1)) a) (W:=quantumOccupationTripleSpace n l m c)
        (typeAFiniteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a)
        (typeAMixedTriple q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m c) := by
  let A := quantumOccupationSpace ℝ (Fin (n+1)) a
  let L := quantumOccupationSpace ℝ (Fin (n+1)) l
  let M := quantumOccupationSpace ℝ (Fin (n+1)) m
  let C := quantumOccupationSpace ℝ (Fin (n+1)) c
  letI : AddCommGroup A := inferInstance
  letI : Module ℝ A := inferInstance
  letI : AddCommGroup L := inferInstance
  letI : Module ℝ L := inferInstance
  letI : AddCommGroup M := inferInstance
  letI : Module ℝ M := inferInstance
  letI : AddCommGroup C := inferInstance
  letI : Module ℝ C := inferInstance
  let B := L ⊗[ℝ] M
  letI : AddCommGroup B := inferInstance
  letI : Module ℝ B := inferInstance
  let rho := typeAFiniteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a
  let sig := typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m
  let tau := typeAFiniteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n c
  let kap := typeAOppositeSymmetricRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n m
  let eta := typeAFiniteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l
  exact (symmetricRightHomBending (X:=A) (W:=B) q hq hq1 n c rho sig).trans
    (algebraIntertwinerTargetEquiv (V:=A) (W:=B ⊗[ℝ] C) (Z:=L ⊗[ℝ] (M ⊗[ℝ] C))
      rho (typeATensorRepresentation q (ne_of_gt hq) n sig tau)
      (typeAMixedTriple q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m c)
      (TensorProduct.assoc ℝ L M C)
      (typeA_associator_intertwines q (ne_of_gt hq) n eta kap tau))

end AMSPhysical
#print axioms AMSPhysical.mixedPairTripleHomEquiv
