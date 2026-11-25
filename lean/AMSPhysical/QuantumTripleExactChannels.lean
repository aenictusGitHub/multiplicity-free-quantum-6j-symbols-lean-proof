import QuantumTripleRadialTensor
import TensorEigenspace
import LinearEigenspaceTransport

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def physicalTripleLeftChannel (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n l m c : ℕ)
    (r : MixedFusionIndex (l+1) (m+1)) : Submodule ℝ (quantumOccupationTripleSpace n (l+1) (m+1) c) :=
  (LinearMap.range (TensorProduct.map (mixedFusionChannelAt q hq hD n (l+1) (m+1) r).subtype
    (LinearMap.id : Module.End ℝ (quantumOccupationSpace ℝ (Fin (n+1)) c)))).map
      (TensorProduct.assoc ℝ _ _ _).toLinearMap

def physicalTripleRightChannel (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n l m c : ℕ)
    (r : MixedFusionIndex (m+1) (c+1)) : Submodule ℝ (quantumOccupationTripleSpace n l (m+1) (c+1)) :=
  LinearMap.range (TensorProduct.map (LinearMap.id : Module.End ℝ (quantumOccupationSpace ℝ (Fin (n+1)) l))
    (reverseMixedFusionChannelAt q hq hD n (m+1) (c+1) r).subtype)

theorem finiteTripleRightRadial_eigenspace (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m c : ℕ) (r : MixedFusionIndex (m+1) (c+1)) :
    Module.End.eigenspace (R:=ℝ) (M:=quantumOccupationTripleSpace n l (m+1) (c+1))
      (finiteTripleRightRadial q n l m c) (quantumCupLeftEigenvalue q n (m+1) (c+1) 0 r.val)=
      physicalTripleRightChannel q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m c r := by
  let V := quantumOccupationSpace ℝ (Fin (n+1)) l
  let W := quantumOccupationSpace ℝ (Fin (n+1)) (m+1) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (c+1)
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  letI : AddCommGroup W := inferInstance
  letI : Module ℝ W := inferInstance
  rw [finiteTripleRightRadial_tensor q hq hq1,
    tensorEigenspace_right (V:=V) (W:=W) (reverseMixedRawRadial q n m c),
    reverseMixedRawRadial_eigenspace q hq hq1 n hn]
  rfl

theorem finiteTripleLeftRadial_eigenspace (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m c : ℕ) (r : MixedFusionIndex (l+1) (m+1)) :
    Module.End.eigenspace (R:=ℝ) (M:=quantumOccupationTripleSpace n (l+1) (m+1) c)
      (finiteTripleLeftRadial q n l m c) (quantumCupLeftEigenvalue q n (l+1) (m+1) 0 r.val)=
      physicalTripleLeftChannel q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m c r := by
  let P := quantumOccupationSpace ℝ (Fin (n+1)) (l+1) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (m+1)
  let C := quantumOccupationSpace ℝ (Fin (n+1)) c
  letI : AddCommGroup P := inferInstance
  letI : Module ℝ P := inferInstance
  letI : AddCommGroup C := inferInstance
  letI : Module ℝ C := inferInstance
  let V := P ⊗[ℝ] C
  let W := quantumOccupationTripleSpace n (l+1) (m+1) c
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  letI : AddCommGroup W := inferInstance
  letI : Module ℝ W := inferInstance
  have ht:=eigenspace_map_intertwiner (V:=V) (W:=W) (TensorProduct.assoc ℝ _ _ _)
    (TensorProduct.map (mixedFiniteRawRadial q n l m) (LinearMap.id : Module.End ℝ (quantumOccupationSpace ℝ (Fin (n+1)) c)))
    (finiteTripleLeftRadial q n l m c)
    (fun v =>by rw [finiteTripleLeftRadial_tensor q hq hq1,LinearEquiv.symm_apply_apply])
    (quantumCupLeftEigenvalue q n (l+1) (m+1) 0 r.val)
  rw [← ht,tensorEigenspace_left (V:=P) (W:=C) (mixedFiniteRawRadial q n l m),mixedFiniteRawRadial_eigenspace q hq hq1 n hn]
  rfl

end AMSPhysical
#print axioms AMSPhysical.finiteTripleLeftRadial_eigenspace
#print axioms AMSPhysical.finiteTripleRightRadial_eigenspace
