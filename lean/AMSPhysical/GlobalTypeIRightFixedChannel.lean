import GlobalTypeIRightStep
import GlobalTypeIIRightFixedChannel

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def globalTypeIRightVector (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a p s r : ℕ) (hs : s≤a) :=
  physicalTypeIRightCoupling q hq hq1 (h+1) (by omega) a (s+r) 0 (p+r) (by omega) (Or.inl rfl)
    (globalTypeIIRightCupIndex a p s r hs)

theorem globalTypeIRightCupIndex_pair (a p s r : ℕ) (hs : s≤a) :
    physicalTypeIRightIndex a (s+r) 0 (p+r) (globalTypeIIRightCupIndex a p s r hs) =
      globalMixedPairIndex s p r := by
  apply Fin.ext
  simp only [physicalTypeIRightIndex,globalTypeIIRightCupIndex,globalMixedPairIndex]
  omega

theorem globalTypeIRightVector_mem (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a p s r : ℕ) (hs : s≤a) :
    (globalTypeIRightVector q hq hq1 h a p s r hs).val ∈
      LinearMap.range (TensorProduct.map
        (LinearMap.id : quantumOccupationSpace ℝ (Fin (h+2)) a →ₗ[ℝ] _)
        (globalReverseMixedPairRealization q hq hq1 (h+1) (by omega) p s r).channel.subtype) := by
  have hv:=physicalTypeIRightCoupling_mem_channel q hq hq1 (h+1) (by omega) a (s+r) 0 (p+r)
    (by omega) (Or.inl rfl) (globalTypeIIRightCupIndex a p s r hs)
  change (globalTypeIRightVector q hq hq1 h a p s r hs).val ∈
    physicalTripleRightChannelGeneral q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      (h+1) a (s+r) (p+r) _ at hv
  rw [physicalTripleRightChannelGeneral_actual q hq hq1 (h+1) (by omega)] at hv
  let S:=reverseMixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1)
    (s+r) (p+r) (physicalTypeIRightIndex a (s+r) 0 (p+r) (globalTypeIIRightCupIndex a p s r hs))
  let T:=(globalReverseMixedPairRealization q hq hq1 (h+1) (by omega) p s r).channel
  have hST : S=T := by
    dsimp only [S,T]
    rw [globalTypeIRightCupIndex_pair,globalReverseMixedPairRealization_channel]
  have he:=tensorRight_range_congr (A:=quantumOccupationSpace ℝ (Fin (h+2)) a) S T hST
  change (globalTypeIRightVector q hq hq1 h a p s r hs).val∈
    LinearMap.range (TensorProduct.map LinearMap.id S.subtype) at hv
  rw [he] at hv
  exact hv

theorem globalTypeIRightVector_creation (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a p s r : ℕ) (hs : s≤a) :
    finiteTripleRightCreation q (h+1) a (s+r) (p+r)
      (globalTypeIRightVector q hq hq1 h a p s r hs).val =
      mixedCreationUnitScale q (h+1) (s+r) (p+r) (globalMixedPairIndex s p r) •
        (globalTypeIRightVector q hq hq1 h a p s (r+1) hs).val := by
  have he:=physicalTypeIRightCoupling_creation q hq hq1 (h+1) (by omega) a (s+r) (p+r)
    (by omega) (globalTypeIIRightCupIndex a p s r hs)
  rw [typeIRightCreationScale,globalTypeIRightCupIndex_pair,← mixedCreationUnitScale_eq_sqrt q hq] at he
  exact he

theorem globalTypeIRightVector_step_transfer (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a p s r : ℕ) (hs : s≤a) :
    (globalTypeIRightVector q hq hq1 h a p s (r+1) hs).val =
      TensorProduct.map (LinearMap.id : quantumOccupationSpace ℝ (Fin (h+2)) a →ₗ[ℝ] _)
        (globalReverseMixedPairTransfer q hq hq1 (h+1) (by omega) p s r (r+1))
        (globalTypeIRightVector q hq hq1 h a p s r hs).val := by
  have hc:=tensorRight_equal_on_channel
    (globalReverseMixedPairRealization q hq hq1 (h+1) (by omega) p s r).channel
    (reverseMixedFiniteCreation q (h+1) (s+r) (p+r))
    (globalReverseMixedPairTransfer q hq hq1 (h+1) (by omega) p s r (r+1))
    (mixedCreationUnitScale q (h+1) (s+r) (p+r) (globalMixedPairIndex s p r))
    (fun x hx=>globalReverseMixedPair_creation_transfer q hq hq1 (h+1) (by omega) p s r ⟨x,hx⟩)
    (globalTypeIRightVector q hq hq1 h a p s r hs).val
    (globalTypeIRightVector_mem q hq hq1 h a p s r hs)
  rw [← finiteTripleRightCreation_tensor,globalTypeIRightVector_creation] at hc
  exact smul_right_injective _ (ne_of_gt (mixedCreationUnitScale_pos q hq (h+1) (s+r) (p+r)
    (globalMixedPairIndex s p r))) hc

/-- The entire Type-I right highest family uses one fixed outer vertex,
independent of the chosen reversed mixed-pair realization. -/
theorem globalTypeIRightVector_from_zero (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a p s r : ℕ) (hs : s≤a) :
    (globalTypeIRightVector q hq hq1 h a p s r hs).val =
      TensorProduct.map (LinearMap.id : quantumOccupationSpace ℝ (Fin (h+2)) a →ₗ[ℝ] _)
        (globalReverseMixedPairTransfer q hq hq1 (h+1) (by omega) p s 0 r)
        (globalTypeIRightVector q hq hq1 h a p s 0 hs).val := by
  induction r with
  | zero =>
    symm
    exact tensorRight_identity_on_channel
      (globalReverseMixedPairRealization q hq hq1 (h+1) (by omega) p s 0).channel
      (globalReverseMixedPairTransfer q hq hq1 (h+1) (by omega) p s 0 0)
      (fun x hx=>globalReverseMixedPairTransfer_self_on_channel q hq hq1 (h+1) (by omega) p s 0 ⟨x,hx⟩)
      _ (globalTypeIRightVector_mem q hq hq1 h a p s 0 hs)
  | succ r ih =>
    rw [globalTypeIRightVector_step_transfer,ih,tensorRight_map_comp,globalReverseMixedPairTransfer_comp]

end AMSPhysical
#print axioms AMSPhysical.globalTypeIRightVector_from_zero
