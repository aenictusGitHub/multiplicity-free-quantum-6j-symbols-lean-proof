import RankTwoCouplingTreeImages
import QuantumTripleRadialTensor
import TensorEigenImage

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

/-- The actual standard left Clebsch tree is an eigenvector of the literal
physical pair radial after the independently proved rank-two module map. -/
theorem rankTwoLeftTree_radial (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m c : ℕ)
    (r : MixedFusionIndex (l+1) (m+1)) (s : Fin (min (coupledLabel (l+1) (m+1) r) c+1))
    (v : RealQuantumSpace (coupledLabel (coupledLabel (l+1) (m+1) r) c s)) :
    finiteTripleLeftRadial q 1 l m c
      (rankTwoMixedTripleEquiv (l+1) (m+1) c (quantumLeftTreeMap q hq hq1 (l+1) (m+1) c r s v))=
      quantumCupLeftEigenvalue q 1 (l+1) (m+1) 0 r.val •
        rankTwoMixedTripleEquiv (l+1) (m+1) c (quantumLeftTreeMap q hq hq1 (l+1) (m+1) c r s v) := by
  let X := quantumOccupationSpace ℝ (Fin 2) (l+1) ⊗[ℝ] quantumOccupationSpace ℝ (Fin 2) (m+1)
  let Y := quantumOccupationSpace ℝ (Fin 2) c
  letI : AddCommGroup X := inferInstance
  letI : Module ℝ X := inferInstance
  letI : AddCommGroup Y := inferInstance
  letI : Module ℝ Y := inferInstance
  have hL (w : RealQuantumSpace (coupledLabel (l+1) (m+1) r)) :
      mixedFiniteRawRadial q 1 l m (rankTwoMixedClebsch q hq hq1 (l+1) (m+1) r w)=
        quantumCupLeftEigenvalue q 1 (l+1) (m+1) 0 r.val • rankTwoMixedClebsch q hq hq1 (l+1) (m+1) r w :=
    mixedFiniteRawRadial_channel q hq hq1 1 (by omega) l m r _
      (rankTwoMixedClebsch_channel q hq hq1 (l+1) (m+1) r w)
  simp only [rankTwoLeftTree_image]
  rw [finiteTripleLeftRadial_tensor q hq hq1,LinearEquiv.symm_apply_apply,
    tensorEigenImage_left (X:=X) (Y:=Y) (rankTwoMixedClebsch q hq hq1 (l+1) (m+1) r)
      (rankTwoSymmetricEquiv c).toLinearMap (mixedFiniteRawRadial q 1 l m) _ hL,map_smul]

theorem rankTwoRightTree_radial (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m c : ℕ)
    (r : MixedFusionIndex (m+1) (c+1)) (s : Fin (min l (coupledLabel (m+1) (c+1) r)+1))
    (v : RealQuantumSpace (coupledLabel l (coupledLabel (m+1) (c+1) r) s)) :
    finiteTripleRightRadial q 1 l m c
      (rankTwoMixedTripleEquiv l (m+1) (c+1) (quantumRightTreeMap q hq hq1 l (m+1) (c+1) r s v))=
      quantumCupLeftEigenvalue q 1 (m+1) (c+1) 0 r.val •
        rankTwoMixedTripleEquiv l (m+1) (c+1) (quantumRightTreeMap q hq hq1 l (m+1) (c+1) r s v) := by
  let X := quantumOccupationSpace ℝ (Fin 2) l
  let Y := quantumOccupationSpace ℝ (Fin 2) (m+1) ⊗[ℝ] quantumOccupationSpace ℝ (Fin 2) (c+1)
  letI : AddCommGroup X := inferInstance
  letI : Module ℝ X := inferInstance
  letI : AddCommGroup Y := inferInstance
  letI : Module ℝ Y := inferInstance
  have hR (w : RealQuantumSpace (coupledLabel (m+1) (c+1) r)) :
      reverseMixedRawRadial q 1 m c (rankTwoReverseMixedClebsch q hq hq1 (m+1) (c+1) r w)=
        quantumCupLeftEigenvalue q 1 (m+1) (c+1) 0 r.val • rankTwoReverseMixedClebsch q hq hq1 (m+1) (c+1) r w :=
    reverseMixedRawRadial_channel q hq hq1 1 (by omega) m c r _
      (rankTwoReverseMixedClebsch_channel q hq hq1 (m+1) (c+1) r w)
  simp only [rankTwoRightTree_image]
  rw [finiteTripleRightRadial_tensor q hq hq1]
  exact tensorEigenImage_right (X:=X) (Y:=Y) (rankTwoSymmetricEquiv l).toLinearMap
    (rankTwoReverseMixedClebsch q hq hq1 (m+1) (c+1) r) (reverseMixedRawRadial q 1 m c) _ hR _

end AMSPhysical
#print axioms AMSPhysical.rankTwoLeftTree_radial
#print axioms AMSPhysical.rankTwoRightTree_radial
