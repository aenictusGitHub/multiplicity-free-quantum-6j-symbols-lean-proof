import QuantumTypeAHomBending
import QuantumPhysicalSnake

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct
variable {X W : Type*}
  [AddCommGroup X] [Module ℝ X] [AddCommGroup W] [Module ℝ W]

def symmetricRightHomBending (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n c : ℕ)
    (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ X) (σ : UqTypeA q n →ₐ[ℝ] Module.End ℝ W) :
    algebraIntertwinerSpace
      (typeATensorRepresentation q (ne_of_gt hq) n ρ
        (typeAOppositeSymmetricRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n c)) σ ≃ₗ[ℝ]
      algebraIntertwinerSpace ρ
        (typeATensorRepresentation q (ne_of_gt hq) n σ
          (typeAFiniteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n c)) := by
  let V := quantumOccupationSpace ℝ (Fin (n+1)) c
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  let b : Module.Basis (occupationWeights (Fin (n+1)) c) ℝ V := quantumOccupationBasis c
  apply typeARightBendingEquiv q (ne_of_gt hq) n ρ σ
    (typeAFiniteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n c)
    (typeAOppositeSymmetricRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n c)
    b (fun x =>occupationDualSign n c x/occupationOppositeWeight q n c x)
    (fun x =>occupationDualSign n c x*occupationOppositeWeight q n c x)
  · intro x
    exact signed_duality_coefficient _ _ (ne_of_gt (occupationOppositeWeight_pos q hq n c x))
      (occupationDualSign_square n c x)
  · exact symmetricReverseCoevaluation_invariant q hq hq1 n c
  · intro z v
    rw [← symmetricPhysicalEvaluation_eq_diagonal]
    exact symmetricPhysicalEvaluation_invariant q hq hq1 n c z v

end AMSPhysical
#print axioms AMSPhysical.symmetricRightHomBending
