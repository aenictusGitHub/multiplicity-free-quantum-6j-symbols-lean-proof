import GlobalTypeIIRightStep
import GlobalMixedPairTransfers
import TensorRightOnChannel

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def globalTypeIIRightCupIndex (a p s r : ℕ) (hs : s≤a) : QuantumCupIndex a (s+r) (p+r) :=
  ⟨⟨s,by omega⟩,by change s≤a ∧ s+r-s≤p+r;omega⟩

theorem globalTypeIIRightCupIndex_pair (a p s r : ℕ) (hs : s≤a) :
    typeIIRightIndex a (p+r) (s+r) (globalTypeIIRightCupIndex a p s r hs) =
      globalMixedPairIndex p s r := by
  apply Fin.ext
  simp only [typeIIRightIndex,mixedFusionSwapIndex,physicalTypeIRightIndex,
    globalTypeIIRightCupIndex,globalMixedPairIndex]
  omega

def globalTypeIIRightVector (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a p s d : ℕ) (hbal : a+p=s+d) (hs : s≤a) (r : ℕ) :=
  physicalTypeIICalibratedRight q hq hq1 h a (p+r) (s+r) d (by omega)
    (globalTypeIIRightCupIndex a p s r hs)

theorem globalTypeIIRightVector_mem (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a p s d : ℕ) (hbal : a+p=s+d) (hs : s≤a) (r : ℕ) :
    (globalTypeIIRightVector q hq hq1 h a p s d hbal hs r).val ∈
      LinearMap.range (TensorProduct.map
        (LinearMap.id : quantumOccupationSpace ℝ (Fin (h+2)) a →ₗ[ℝ] _)
        (globalMixedPairRealization q hq hq1 (h+1) (by omega) p s r).channel.subtype) := by
  have hv:=physicalTypeIICalibratedRight_mem q hq hq1 h a (p+r) (s+r) d (by omega)
    (globalTypeIIRightCupIndex a p s r hs)
  let S:=mixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1)
    (p+r) (s+r) (typeIIRightIndex a (p+r) (s+r) (globalTypeIIRightCupIndex a p s r hs))
  let T:=(globalMixedPairRealization q hq hq1 (h+1) (by omega) p s r).channel
  have hST : S=T := by
    dsimp only [S,T]
    rw [globalTypeIIRightCupIndex_pair,globalMixedPairRealization_channel]
  have he:=tensorRight_range_congr
    (A:=quantumOccupationSpace ℝ (Fin (h+2)) a) S T hST
  change (globalTypeIIRightVector q hq hq1 h a p s d hbal hs r).val∈
    LinearMap.range (TensorProduct.map LinearMap.id S.subtype) at hv
  rw [he] at hv
  exact hv

theorem globalTypeIIRightVector_creation (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a p s d : ℕ) (hbal : a+p=s+d) (hs : s≤a) (r : ℕ) :
    physicalTypeIIRightCreation q (h+1) a (p+r) (s+r)
      (globalTypeIIRightVector q hq hq1 h a p s d hbal hs r).val =
      mixedCreationUnitScale q (h+1) (p+r) (s+r) (globalMixedPairIndex p s r) •
        (globalTypeIIRightVector q hq hq1 h a p s d hbal hs (r+1)).val := by
  have he:=congrArg Subtype.val (physicalTypeIICalibratedRight_creation q hq hq1 h a (p+r) (s+r) d
    (by omega) (globalTypeIIRightCupIndex a p s r hs))
  simp only [Submodule.coe_smul_of_tower] at he
  change physicalTypeIIRightCreation q (h+1) a (p+r) (s+r) _ = _ at he
  rw [typeIIRightCreationScale,globalTypeIIRightCupIndex_pair,← mixedCreationUnitScale_eq_sqrt q hq] at he
  exact he

theorem globalTypeIIRightVector_step_transfer (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a p s d : ℕ) (hbal : a+p=s+d) (hs : s≤a) (r : ℕ) :
    (globalTypeIIRightVector q hq hq1 h a p s d hbal hs (r+1)).val =
      TensorProduct.map (LinearMap.id : quantumOccupationSpace ℝ (Fin (h+2)) a →ₗ[ℝ] _)
        (globalMixedPairTransfer q hq hq1 (h+1) (by omega) p s r (r+1))
        (globalTypeIIRightVector q hq hq1 h a p s d hbal hs r).val := by
  have hc:=tensorRight_equal_on_channel
    (globalMixedPairRealization q hq hq1 (h+1) (by omega) p s r).channel
    (mixedFiniteCreation q (h+1) (p+r) (s+r))
    (globalMixedPairTransfer q hq hq1 (h+1) (by omega) p s r (r+1))
    (mixedCreationUnitScale q (h+1) (p+r) (s+r) (globalMixedPairIndex p s r))
    (fun x hx =>globalMixedPair_creation_transfer q hq hq1 (h+1) (by omega) p s r ⟨x,hx⟩)
    (globalTypeIIRightVector q hq hq1 h a p s d hbal hs r).val
    (globalTypeIIRightVector_mem q hq hq1 h a p s d hbal hs r)
  change physicalTypeIIRightCreation q (h+1) a (p+r) (s+r) _ = _ at hc
  rw [globalTypeIIRightVector_creation] at hc
  exact smul_right_injective _ (ne_of_gt (mixedCreationUnitScale_pos q hq (h+1) (p+r) (s+r)
    (globalMixedPairIndex p s r))) hc

/-- Every Type-II right coupling with a given internal highest weight is
transported from the same contraction-zero vector. The second vertex has
no dependence on the exterior mixed-pair realization. -/
theorem globalTypeIIRightVector_from_zero (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a p s d : ℕ) (hbal : a+p=s+d) (hs : s≤a) (r : ℕ) :
    (globalTypeIIRightVector q hq hq1 h a p s d hbal hs r).val =
      TensorProduct.map (LinearMap.id : quantumOccupationSpace ℝ (Fin (h+2)) a →ₗ[ℝ] _)
        (globalMixedPairTransfer q hq hq1 (h+1) (by omega) p s 0 r)
        (globalTypeIIRightVector q hq hq1 h a p s d hbal hs 0).val := by
  induction r with
  | zero =>
    symm
    exact tensorRight_identity_on_channel
      (globalMixedPairRealization q hq hq1 (h+1) (by omega) p s 0).channel
      (globalMixedPairTransfer q hq hq1 (h+1) (by omega) p s 0 0)
      (fun x hx =>globalMixedPairTransfer_self_on_channel q hq hq1 (h+1) (by omega) p s 0 ⟨x,hx⟩)
      _ (globalTypeIIRightVector_mem q hq hq1 h a p s d hbal hs 0)
  | succ r ih =>
    rw [globalTypeIIRightVector_step_transfer,ih,tensorRight_map_comp,globalMixedPairTransfer_comp]

end AMSPhysical
#print axioms AMSPhysical.globalTypeIIRightVector_step_transfer
#print axioms AMSPhysical.globalTypeIIRightVector_from_zero
