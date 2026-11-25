import PhysicalTypeIRightCreationGeometry
import TensorLeftOnChannel
import QuantumTripleLeftTensorMetric

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem finiteTripleLeftCreation_gram_channel (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m c : ℕ) (r : MixedFusionIndex l m)
    (v w : quantumOccupationTripleSpace n l m c)
    (hv : v∈physicalTripleLeftChannelGeneral q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m c r)
    (hw : w∈physicalTripleLeftChannelGeneral q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m c r) :
    physicalTripleBilin q n (l+1) (m+1) c
      (finiteTripleLeftCreation q n l m c v) (finiteTripleLeftCreation q n l m c w) =
      mixedCreationSpectralScalar q n l m r.val*physicalTripleBilin q n l m c v w := by
  rw [physicalTripleLeftChannelGeneral_actual q hq hq1 n hn] at hv hw
  obtain ⟨v,⟨u,rfl⟩,rfl⟩:=hv
  obtain ⟨w,⟨z,rfl⟩,rfl⟩:=hw
  let S:=mixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m r
  have he:=tensorWeightedBilin_left_carrier_scale
    ((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l).tensorProduct
      (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m))
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) c)
    ((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) (l+1)).tensorProduct
      (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) (m+1)))
    (fun xy=>occupationCompactWeight q n l xy.1*occupationOppositeWeight q n m xy.2)
    (occupationCompactWeight q n c)
    (fun xy=>occupationCompactWeight q n (l+1) xy.1*occupationOppositeWeight q n (m+1) xy.2)
    S.subtype ((mixedFiniteCreation q n l m).comp S.subtype)
    (mixedCreationSpectralScalar q n l m r.val)
    (fun x y=>mixedFiniteCreation_gram_channel q hq hq1 n hn l m r x.val y.val y.property) u z
  rw [finiteTripleLeftCreation_tensor]
  simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply]
  rw [physicalTriple_assoc_isometry,physicalTriple_assoc_isometry,tensorLeft_map_comp,tensorLeft_map_comp]
  exact he

theorem physicalTypeILeftIndex_creation (l m c : ℕ) (t : QuantumCupIndex l m c) :
    physicalTypeILeftIndex (l+1) (m+1) 0 c (cupCreateLeftIndex l m c t) =
      mixedFusionIndexSucc l m (physicalTypeILeftIndex l m 0 c t) := by
  apply Fin.ext
  rfl

theorem finiteTripleLeftCreation_mem_successor (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m c : ℕ) (t : QuantumCupIndex l m c)
    (v : quantumOccupationTripleSpace n l m c)
    (hv : v∈physicalTripleLeftChannelGeneral q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      n l m c (physicalTypeILeftIndex l m 0 c t)) :
    finiteTripleLeftCreation q n l m c v∈physicalTripleLeftChannelGeneral q (ne_of_gt hq)
      (qInteger_denominator_ne_zero q hq hq1) n (l+1) (m+1) c
      (physicalTypeILeftIndex (l+1) (m+1) 0 c (cupCreateLeftIndex l m c t)) := by
  rw [physicalTripleLeftChannelGeneral_actual q hq hq1 n hn] at hv ⊢
  obtain ⟨v,⟨u,rfl⟩,rfl⟩:=hv
  rw [finiteTripleLeftCreation_tensor]
  simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply]
  let X:=mixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
    n l m (physicalTypeILeftIndex l m 0 c t)
  let Y:=mixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
    n (l+1) (m+1) (physicalTypeILeftIndex (l+1) (m+1) 0 c (cupCreateLeftIndex l m c t))
  let F : X →ₗ[ℝ] Y := ((mixedFiniteCreation q n l m).comp X.subtype).codRestrict Y (by
    intro x
    dsimp only [LinearMap.comp_apply,Submodule.subtype_apply,Y]
    rw [physicalTypeILeftIndex_creation]
    exact mixedFiniteCreation_mem_successor_channel q hq hq1 n hn l m
      (physicalTypeILeftIndex l m 0 c t) x.val x.property)
  refine ⟨TensorProduct.map Y.subtype LinearMap.id (TensorProduct.map F LinearMap.id u),
    ⟨TensorProduct.map F LinearMap.id u,rfl⟩,?_⟩
  apply congrArg (fun w => (TensorProduct.assoc ℝ
    (quantumOccupationSpace ℝ (Fin (n+1)) (l+1))
    (quantumOccupationSpace ℝ (Fin (n+1)) (m+1))
    (quantumOccupationSpace ℝ (Fin (n+1)) c)) w)
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u w hu hw => simp only [map_add,hu,hw]
  | tmul x y => rfl

def physicalTypeIHighestLeftCreation (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n l m c : ℕ) :
    physicalQuantumHighestMultiplicity q hq hD n l m 0 c →ₗ[ℝ]
      physicalQuantumHighestMultiplicity q hq hD n (l+1) (m+1) 0 c := by
  let ρ:=typeAMixedTriple q hq hD n l m c
  let σ:=typeAMixedTriple q hq hD n (l+1) (m+1) c
  have he : mixedHighestDynkin n (l+c-m+0) 0 = mixedHighestDynkin n ((l+1)+c-(m+1)+0) 0 := by
    congr 1
    omega
  exact (LinearEquiv.ofEq _ _ (congrArg (typeAHighestSpace q n σ) he)).toLinearMap.comp
    (typeAHighestSpaceMap q n ρ σ (finiteTripleLeftCreation q n l m c)
      (finiteTripleLeftCreation_intertwines q hq hD n l m c) (mixedHighestDynkin n (l+c-m+0) 0))

theorem physicalTypeIHighestLeftCreation_val (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n l m c : ℕ)
    (v : physicalQuantumHighestMultiplicity q hq hD n l m 0 c) :
    (physicalTypeIHighestLeftCreation q hq hD n l m c v).val=finiteTripleLeftCreation q n l m c v.val := rfl

end AMSPhysical
#print axioms AMSPhysical.finiteTripleLeftCreation_gram_channel
#print axioms AMSPhysical.finiteTripleLeftCreation_mem_successor
