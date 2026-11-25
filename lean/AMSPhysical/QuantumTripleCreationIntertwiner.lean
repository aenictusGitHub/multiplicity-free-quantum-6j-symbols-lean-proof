import QuantumTypeAMixedTriple
import QuantumTypeATripleIntertwiner

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem finiteTripleRightCreation_intertwines (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n l m c : ℕ)
    (z : UqTypeA q n) (v : quantumOccupationTripleSpace n l m c) :
    finiteTripleRightCreation q n l m c (typeAMixedTriple q hq hD n l m c z v)=
      typeAMixedTriple q hq hD n l (m+1) (c+1) z (finiteTripleRightCreation q n l m c v) := by
  let V := quantumOccupationSpace ℝ (Fin (n+1)) l
  let W := quantumOccupationSpace ℝ (Fin (n+1)) m ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) c
  let W' := quantumOccupationSpace ℝ (Fin (n+1)) (m+1) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (c+1)
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  letI : AddCommGroup W := inferInstance
  letI : Module ℝ W := inferInstance
  letI : AddCommGroup W' := inferInstance
  letI : Module ℝ W' := inferInstance
  rw [finiteTripleRightCreation_tensor]
  unfold typeAMixedTriple
  exact typeA_intertwiner_tensor (V:=V) (W:=W) (V':=V) (W':=W') q hq n
    (typeAFiniteQuantumRepresentation q hq hD n l) (typeAReverseMixedTensor q hq hD n m c)
    (typeAFiniteQuantumRepresentation q hq hD n l) (typeAReverseMixedTensor q hq hD n (m+1) (c+1))
    LinearMap.id (reverseMixedFiniteCreation q n m c) (fun _ _ =>rfl)
    (reverseMixedFiniteCreation_intertwines q hq hD n m c) z v

set_option maxHeartbeats 1200000 in
theorem finiteTripleLeftCreation_intertwines (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n l m c : ℕ)
    (z : UqTypeA q n) (v : quantumOccupationTripleSpace n l m c) :
    finiteTripleLeftCreation q n l m c (typeAMixedTriple q hq hD n l m c z v)=
      typeAMixedTriple q hq hD n (l+1) (m+1) c z (finiteTripleLeftCreation q n l m c v) := by
  let V := quantumOccupationSpace ℝ (Fin (n+1)) l
  let W := quantumOccupationSpace ℝ (Fin (n+1)) m
  let U := quantumOccupationSpace ℝ (Fin (n+1)) c
  let V' := quantumOccupationSpace ℝ (Fin (n+1)) (l+1)
  let W' := quantumOccupationSpace ℝ (Fin (n+1)) (m+1)
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  letI : AddCommGroup W := inferInstance
  letI : Module ℝ W := inferInstance
  letI : AddCommGroup U := inferInstance
  letI : Module ℝ U := inferInstance
  letI : AddCommGroup V' := inferInstance
  letI : Module ℝ V' := inferInstance
  letI : AddCommGroup W' := inferInstance
  letI : Module ℝ W' := inferInstance
  let P := V ⊗[ℝ] W
  let P' := V' ⊗[ℝ] W'
  letI : AddCommGroup P := inferInstance
  letI : Module ℝ P := inferInstance
  letI : AddCommGroup P' := inferInstance
  letI : Module ℝ P' := inferInstance
  rw [finiteTripleLeftCreation_tensor]
  simp only [LinearMap.comp_apply,LinearEquiv.coe_coe]
  unfold typeAMixedTriple typeAReverseMixedTensor
  exact typeA_associatedTensorIntertwiner (V:=V) (W:=W) (U:=U) (V':=V') (W':=W') (U':=U) q hq n
    (typeAFiniteQuantumRepresentation q hq hD n l) (typeAOppositeSymmetricRepresentation q hq hD n m)
    (typeAFiniteQuantumRepresentation q hq hD n c)
    (typeAFiniteQuantumRepresentation q hq hD n (l+1)) (typeAOppositeSymmetricRepresentation q hq hD n (m+1))
    (typeAFiniteQuantumRepresentation q hq hD n c)
    (mixedFiniteCreation q n l m) LinearMap.id (mixedFiniteCreation_intertwines q hq hD n l m) (fun _ _ =>rfl) z v

end AMSPhysical
#print axioms AMSPhysical.finiteTripleLeftCreation_intertwines
#print axioms AMSPhysical.finiteTripleRightCreation_intertwines
