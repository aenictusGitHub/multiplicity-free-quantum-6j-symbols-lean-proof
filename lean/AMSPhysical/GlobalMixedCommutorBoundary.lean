import GlobalReverseMixedPairTransfers
import QuantumMixedCommutorChannels
import PhysicalAllFirstFunctional
import GlobalTypeIIRightFixedChannel

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem physicalMixedCommutor_zero_channel (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (p s : ℕ)
    (x : (globalMixedPairRealization q hq hq1 n hn p s 0).channel) :
    physicalMixedCommutor q hq hq1 n hn p s x.val =
      ((globalMixedPairRealization q hq hq1 n hn p s 0).transport (ne_of_gt hq)
        (globalReverseMixedPairRealization q hq hq1 n hn p s 0) x).val := by
  exact orthogonalFusionTransport_channel_apply
    (mixedTensorBilin q n p s) (reverseMixedTensorBilin q n s p)
    (mixedTensorBilin_definite q hq n p s) (reverseMixedTensorBilin_definite q hq n s p)
    (fun r=>(mixedCommutorSourceRealization q hq hq1 n hn p s r).channel)
    (fun r=>(mixedCommutorTargetRealization q hq hq1 n hn p s r).channel)
    (mixedCommutorSource_orthogonal q hq hq1 n hn p s)
    (mixedCommutorTarget_orthogonal q hq hq1 n hn p s)
    (mixedCommutorSource_span q hq hq1 n hn p s)
    (mixedCommutorTarget_span q hq hq1 n hn p s)
    (fun r=>CompactHighestRealization.transport (ne_of_gt hq)
      (mixedCommutorSourceRealization q hq hq1 n hn p s r)
      (mixedCommutorTargetRealization q hq hq1 n hn p s r)) ⟨0,by omega⟩ x

theorem physicalMixedCommutor_zero_boundary (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (p s : ℕ)
    (x : (globalMixedPairRealization q hq hq1 n hn p s 0).channel) :
    reverseMixedFirstBoundaryFunctional n p s (physicalMixedCommutor q hq hq1 n hn p s x.val) =
      q^((p:ℤ)*(s:ℤ))*mixedFirstBoundaryFunctional n p s x.val := by
  rw [physicalMixedCommutor_zero_channel]
  exact globalMixedOrientation_boundary q hq hq1 n hn p s x

theorem physicalTypeIIToI_zero_boundary (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (a p s : ℕ) (v : quantumOccupationTripleSpace n a p s)
    (hv : v∈LinearMap.range (TensorProduct.map
      (LinearMap.id : quantumOccupationSpace ℝ (Fin (n+1)) a →ₗ[ℝ] _)
      (globalMixedPairRealization q hq hq1 n hn p s 0).channel.subtype)) :
    physicalAllFirstFunctional n a s p (physicalTypeIIToI q hq hq1 n hn a p s v) =
      q^((p:ℤ)*(s:ℤ))*physicalAllFirstFunctional n a p s v := by
  obtain ⟨u,rfl⟩:=hv
  rw [physicalAllFirstFunctional_reverseMixed,physicalAllFirstFunctional_mixed]
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u w hu hw => simp only [map_add,hu,hw,mul_add]
  | tmul x y =>
    simp only [LinearMap.comp_apply,physicalTypeIIToI,TensorProduct.congr_tmul,
      LinearEquiv.refl_apply,TensorProduct.map_tmul,LinearMap.id_apply,Submodule.subtype_apply,
      tensorFirstFunctional_tmul,map_smul,smul_eq_mul]
    rw [physicalMixedCommutor_zero_boundary q hq hq1 n hn p s y]
    ring

theorem globalTypeIIRightVector_first_boundary_pos (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a p s d : ℕ) (hbal : a+p=s+d) (hs : s≤a) (r : ℕ) :
    0 < physicalAllFirstFunctional (h+1) a (p+r) (s+r)
      (globalTypeIIRightVector q hq hq1 h a p s d hbal hs r).val := by
  have hp:=physicalTypeIICalibratedRight_first_boundary_pos q hq hq1 h a (p+r) (s+r) d
    (by omega) (globalTypeIIRightCupIndex a p s r hs)
  rw [← standardBoundaryCoordinate_eq_typeIISelected] at hp
  simp only [typeIIZeroCommonIndex,Fin.val_mk,Nat.add_zero] at hp
  have he:=DFunLike.congr_fun (physicalAllFirstFunctional_projection (h+1) (by omega) a (p+r) (s+r))
    (globalTypeIIRightVector q hq hq1 h a p s d hbal hs r).val
  exact he ▸ hp

end AMSPhysical
#print axioms AMSPhysical.physicalTypeIIToI_zero_boundary
