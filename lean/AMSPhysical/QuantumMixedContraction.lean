import QuantumMixedCreationIntertwiner
import QuantumMixedCompact
import CompactJointAdjoint
import FiniteWeightedAdjoint

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 180000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

/-- The actual physical contraction is constructed as the metric adjoint
of the explicit occupation creation map. -/
def mixedFiniteContraction (q : ℝ) (hq : 0<q) (n l m : ℕ) :
    (quantumOccupationSpace ℝ (Fin (n+1)) (l+1) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (m+1)) →ₗ[ℝ]
      (quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) := by
  let V := quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m
  let W := quantumOccupationSpace ℝ (Fin (n+1)) (l+1) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (m+1)
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  letI : AddCommGroup W := inferInstance
  letI : Module ℝ W := inferInstance
  exact finiteWeightedAdjoint (V:=V) (W:=W)
    ((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l).tensorProduct
      (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m))
    ((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) (l+1)).tensorProduct
      (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) (m+1)))
    (fun xy =>occupationCompactWeight q n l xy.1*occupationOppositeWeight q n m xy.2)
    (fun xy =>occupationCompactWeight q n (l+1) xy.1*occupationOppositeWeight q n (m+1) xy.2)
    (fun xy =>mul_ne_zero (ne_of_gt (occupationCompactWeight_pos q hq n l xy.1))
      (ne_of_gt (occupationOppositeWeight_pos q hq n m xy.2)))
    (mixedFiniteCreation q n l m)

theorem mixedFiniteContraction_adjoint (q : ℝ) (hq : 0<q) (n l m : ℕ)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
    (w : quantumOccupationSpace ℝ (Fin (n+1)) (l+1) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (m+1)) :
    mixedTensorBilin q n (l+1) (m+1) (mixedFiniteCreation q n l m v) w=
      mixedTensorBilin q n l m v (mixedFiniteContraction q hq n l m w) := by
  let V := quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m
  let W := quantumOccupationSpace ℝ (Fin (n+1)) (l+1) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (m+1)
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  letI : AddCommGroup W := inferInstance
  letI : Module ℝ W := inferInstance
  exact finiteWeightedAdjoint_adjoint (V:=V) (W:=W) _ _ _ _ _ _ _ _

theorem mixedTensorBilin_injective (q : ℝ) (hq : 0<q) (n l m : ℕ) :
    Function.Injective (mixedTensorBilin q n l m) := by
  let V := quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  exact finiteWeightedBilin_injective (V:=V)
    ((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l).tensorProduct
      (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m))
    (fun xy =>occupationCompactWeight q n l xy.1*occupationOppositeWeight q n m xy.2)
    (fun xy =>mul_ne_zero (ne_of_gt (occupationCompactWeight_pos q hq n l xy.1))
      (ne_of_gt (occupationOppositeWeight_pos q hq n m xy.2)))

theorem mixedFiniteContraction_intertwines (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n l m : ℕ) (z : UqTypeA q n)
    (w : quantumOccupationSpace ℝ (Fin (n+1)) (l+1) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (m+1)) :
    mixedFiniteContraction q hq n l m
        (typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n (l+1) (m+1) z w)=
      typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m z
        (mixedFiniteContraction q hq n l m w) := by
  let V := quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m
  let W := quantumOccupationSpace ℝ (Fin (n+1)) (l+1) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (m+1)
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  letI : AddCommGroup W := inferInstance
  letI : Module ℝ W := inferInstance
  exact compact_intertwiner_adjoint (V:=V) (W:=W)
    (mixedTensorBilin q n l m) (mixedTensorBilin q n (l+1) (m+1))
    (typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m)
    (typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n (l+1) (m+1))
    (typeAMixedTensor_compact q hq hq1 n l m) (typeAMixedTensor_compact q hq hq1 n (l+1) (m+1))
    (mixedTensorBilin_injective q hq n l m) (mixedTensorBilin_symm q n l m)
    (mixedTensorBilin_symm q n (l+1) (m+1)) (mixedFiniteCreation q n l m)
    (mixedFiniteContraction q hq n l m)
    (mixedFiniteCreation_intertwines q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m)
    (mixedFiniteContraction_adjoint q hq n l m) z w

end AMSPhysical
#print axioms AMSPhysical.mixedFiniteContraction_intertwines
