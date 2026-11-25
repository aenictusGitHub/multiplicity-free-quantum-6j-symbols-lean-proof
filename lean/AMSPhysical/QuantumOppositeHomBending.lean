import QuantumTypeAHomBending
import QuantumPhysicalSnake

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct
variable {X W : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup W] [Module ℝ W]

/-- Actual right bending with a symmetric input leg and opposite output leg.
This is the orientation required by the Type-II two-row coupling tree. -/
def oppositeRightHomBending (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n c : ℕ)
    (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ X) (σ : UqTypeA q n →ₐ[ℝ] Module.End ℝ W) :
    algebraIntertwinerSpace
      (typeATensorRepresentation q (ne_of_gt hq) n ρ
        (typeAFiniteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n c)) σ ≃ₗ[ℝ]
    algebraIntertwinerSpace ρ
      (typeATensorRepresentation q (ne_of_gt hq) n σ
        (typeAOppositeSymmetricRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n c)) := by
  let V:=quantumOccupationSpace ℝ (Fin (n+1)) c
  letI : AddCommGroup V:=inferInstance
  letI : Module ℝ V:=inferInstance
  let b : Module.Basis (occupationWeights (Fin (n+1)) c) ℝ V:=quantumOccupationBasis c
  apply typeARightBendingEquiv q (ne_of_gt hq) n ρ σ
    (typeAOppositeSymmetricRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n c)
    (typeAFiniteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n c)
    b (fun x =>occupationDualSign n c x/occupationCompactWeight q n c x)
    (fun x =>occupationDualSign n c x*occupationCompactWeight q n c x)
  · intro x
    exact signed_duality_coefficient _ _ (ne_of_gt (occupationCompactWeight_pos q hq n c x))
      (occupationDualSign_square n c x)
  · intro z
    rw [← symmetricCoevaluation_diagonal]
    exact symmetricCoevaluation_invariant q hq hq1 n c z
  · intro z v
    change symmetricReverseEvaluation q n c
      (typeAReverseMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n c c z v)=_
    exact symmetricReverseEvaluation_invariant q hq hq1 n c z v

end AMSPhysical
#print axioms AMSPhysical.oppositeRightHomBending
