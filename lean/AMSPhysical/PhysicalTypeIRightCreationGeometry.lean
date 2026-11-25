import NativeMixedCreationGeometry
import PhysicalTypeIFirstBoundaryCreation
import TensorChannelScaledMetric
import QuantumTripleChannelsActual
import TensorRightOnChannel

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem finiteTripleRightCreation_gram_channel (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m c : ℕ) (r : MixedFusionIndex m c)
    (v w : quantumOccupationTripleSpace n l m c)
    (hv : v∈physicalTripleRightChannelGeneral q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m c r)
    (hw : w∈physicalTripleRightChannelGeneral q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m c r) :
    physicalTripleBilin q n l (m+1) (c+1)
      (finiteTripleRightCreation q n l m c v) (finiteTripleRightCreation q n l m c w) =
      mixedCreationSpectralScalar q n m c r.val*physicalTripleBilin q n l m c v w := by
  rw [physicalTripleRightChannelGeneral_actual q hq hq1 n hn] at hv hw
  obtain ⟨u,rfl⟩:=hv
  obtain ⟨z,rfl⟩:=hw
  let S:=reverseMixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n m c r
  have he:=tensorWeightedBilin_right_carrier_scale
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l)
    ((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m).tensorProduct
      (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) c))
    ((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) (m+1)).tensorProduct
      (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) (c+1)))
    (occupationCompactWeight q n l)
    (fun yz=>occupationOppositeWeight q n m yz.1*occupationCompactWeight q n c yz.2)
    (fun yz=>occupationOppositeWeight q n (m+1) yz.1*occupationCompactWeight q n (c+1) yz.2)
    S.subtype ((reverseMixedFiniteCreation q n m c).comp S.subtype)
    (mixedCreationSpectralScalar q n m c r.val)
    (fun x y=>reverseMixedFiniteCreation_gram_channel q hq hq1 n hn m c r x.val y.val y.property) u z
  rw [finiteTripleRightCreation_tensor,physicalTripleBilin_tensor,physicalTripleBilin_tensor]
  rw [tensorRight_map_comp,tensorRight_map_comp]
  exact he

theorem physicalTypeIRightIndex_creation (l m c : ℕ) (t : QuantumCupIndex l m c) :
    physicalTypeIRightIndex l (m+1) 0 (c+1) (cupCreateRightIndex l m c t) =
      mixedFusionIndexSucc m c (physicalTypeIRightIndex l m 0 c t) := by
  apply Fin.ext
  have ht:=t.val.isLt
  simp only [physicalTypeIRightIndex,cupCreateRightIndex,mixedFusionIndexSucc]
  omega

theorem finiteTripleRightCreation_mem_successor (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m c : ℕ) (t : QuantumCupIndex l m c)
    (v : quantumOccupationTripleSpace n l m c)
    (hv : v∈physicalTripleRightChannelGeneral q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      n l m c (physicalTypeIRightIndex l m 0 c t)) :
    finiteTripleRightCreation q n l m c v∈physicalTripleRightChannelGeneral q (ne_of_gt hq)
      (qInteger_denominator_ne_zero q hq hq1) n l (m+1) (c+1)
      (physicalTypeIRightIndex l (m+1) 0 (c+1) (cupCreateRightIndex l m c t)) := by
  rw [physicalTripleRightChannelGeneral_actual q hq hq1 n hn] at hv ⊢
  obtain ⟨u,hu⟩:=hv
  rw [← hu,finiteTripleRightCreation_tensor]
  let X:=reverseMixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
    n m c (physicalTypeIRightIndex l m 0 c t)
  let Y:=reverseMixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
    n (m+1) (c+1) (physicalTypeIRightIndex l (m+1) 0 (c+1) (cupCreateRightIndex l m c t))
  let F : X →ₗ[ℝ] Y := ((reverseMixedFiniteCreation q n m c).comp X.subtype).codRestrict Y (by
    intro x
    dsimp only [LinearMap.comp_apply,Submodule.subtype_apply,Y]
    rw [physicalTypeIRightIndex_creation]
    exact reverseMixedFiniteCreation_mem_successor_channel q hq hq1 n hn m c
      (physicalTypeIRightIndex l m 0 c t) x.val x.property)
  refine ⟨TensorProduct.map LinearMap.id F u,?_⟩
  clear hu
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u w hu hw => simp only [map_add,hu,hw]
  | tmul x y => rfl

def physicalTypeIHighestRightCreation (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n l m c : ℕ) :
    physicalQuantumHighestMultiplicity q hq hD n l m 0 c →ₗ[ℝ]
      physicalQuantumHighestMultiplicity q hq hD n l (m+1) 0 (c+1) := by
  let ρ:=typeAMixedTriple q hq hD n l m c
  let σ:=typeAMixedTriple q hq hD n l (m+1) (c+1)
  have he : mixedHighestDynkin n (l+c-m+0) 0 = mixedHighestDynkin n (l+(c+1)-(m+1)+0) 0 := by
    congr 1
    omega
  exact (LinearEquiv.ofEq _ _ (congrArg (typeAHighestSpace q n σ) he)).toLinearMap.comp
    (typeAHighestSpaceMap q n ρ σ (finiteTripleRightCreation q n l m c)
      (finiteTripleRightCreation_intertwines q hq hD n l m c) (mixedHighestDynkin n (l+c-m+0) 0))

theorem physicalTypeIHighestRightCreation_val (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n l m c : ℕ)
    (v : physicalQuantumHighestMultiplicity q hq hD n l m 0 c) :
    (physicalTypeIHighestRightCreation q hq hD n l m c v).val=finiteTripleRightCreation q n l m c v.val := rfl

end AMSPhysical
#print axioms AMSPhysical.finiteTripleRightCreation_gram_channel
#print axioms AMSPhysical.finiteTripleRightCreation_mem_successor
