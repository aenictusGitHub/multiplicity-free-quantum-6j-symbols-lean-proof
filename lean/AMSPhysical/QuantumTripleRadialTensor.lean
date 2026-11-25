import QuantumTripleLeftTensorAnnihilation
import QuantumTripleRightTensorAnnihilation
import QuantumMixedExactEigenspaces
import QuantumFiniteTripleRadial

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem finiteTripleRightRadial_tensor (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n l m c : ℕ) :
    finiteTripleRightRadial q n l m c=
      TensorProduct.map (LinearMap.id : Module.End ℝ (quantumOccupationSpace ℝ (Fin (n+1)) l))
        (reverseMixedRawRadial q n m c) := by
  unfold finiteTripleRightRadial reverseMixedRawRadial
  rw [finiteTripleRightCreation_tensor,finiteTripleRightAnnihilation_tensor q hq hq1]
  rw [← TensorProduct.map_comp,LinearMap.id_comp]

theorem finiteTripleLeftRadial_tensor (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n l m c : ℕ)
    (v : quantumOccupationTripleSpace n (l+1) (m+1) c) :
    finiteTripleLeftRadial q n l m c v=
      (TensorProduct.assoc ℝ _ _ _)
        (TensorProduct.map (mixedFiniteRawRadial q n l m) (LinearMap.id : Module.End ℝ (quantumOccupationSpace ℝ (Fin (n+1)) c))
          ((TensorProduct.assoc ℝ _ _ _).symm v)) := by
  unfold finiteTripleLeftRadial
  rw [finiteTripleLeftCreation_tensor,finiteTripleLeftAnnihilation_tensor q hq hq1]
  unfold finiteTripleLeftTensorAnnihilation
  simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply]
  rw [← LinearMap.comp_apply,← TensorProduct.map_comp,LinearMap.id_comp]
  rfl

end AMSPhysical
#print axioms AMSPhysical.finiteTripleRightRadial_tensor
#print axioms AMSPhysical.finiteTripleLeftRadial_tensor
