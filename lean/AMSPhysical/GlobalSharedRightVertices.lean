import GlobalTypeIRightIIComparison

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def globalReverseMixedPairClebsch (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (p s r : ℕ) :=
  (globalReverseMixedPairRealization q hq hq1 n hn p s r).channel.subtype.comp
    ((globalMixedPairRealization q hq hq1 n hn p s 0).transport (ne_of_gt hq)
      (globalReverseMixedPairRealization q hq hq1 n hn p s r)).toLinearMap

theorem globalReverseMixedPairClebsch_apply (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (p s r : ℕ)
    (x : (globalMixedPairRealization q hq hq1 n hn p s 0).channel) :
    globalReverseMixedPairClebsch q hq hq1 n hn p s r x =
      ((globalMixedPairRealization q hq hq1 n hn p s 0).transport (ne_of_gt hq)
        (globalReverseMixedPairRealization q hq hq1 n hn p s r) x).val := rfl

theorem globalReverseMixedPairClebsch_intertwines (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (p s r : ℕ) (z : UqTypeA q n)
    (x : (globalMixedPairRealization q hq hq1 n hn p s 0).channel) :
    globalReverseMixedPairClebsch q hq hq1 n hn p s r
      ((globalMixedPairRealization q hq hq1 n hn p s 0).channelAction z x) =
      typeAReverseMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n (s+r) (p+r) z
        (globalReverseMixedPairClebsch q hq hq1 n hn p s r x) :=
  (globalMixedPairRealization q hq hq1 n hn p s 0).transport_intertwines (ne_of_gt hq)
    (globalReverseMixedPairRealization q hq hq1 n hn p s r) z x

theorem globalReverseMixedPairClebsch_isometry (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (p s r : ℕ)
    (x y : (globalMixedPairRealization q hq hq1 n hn p s 0).channel) :
    reverseMixedTensorBilin q n (s+r) (p+r)
      (globalReverseMixedPairClebsch q hq hq1 n hn p s r x)
      (globalReverseMixedPairClebsch q hq hq1 n hn p s r y) = mixedTensorBilin q n p s x.val y.val :=
  ((globalMixedPairRealization q hq hq1 n hn p s 0).transport_isometry (ne_of_gt hq)
    (globalReverseMixedPairRealization q hq hq1 n hn p s r) x y).symm

theorem globalReverseMixedPairClebsch_factor (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (p s r : ℕ) :
    (globalReverseMixedPairTransfer q hq hq1 n hn p s 0 r).comp
      (globalReverseMixedPairClebsch q hq hq1 n hn p s 0) =
      globalReverseMixedPairClebsch q hq hq1 n hn p s r := by
  apply LinearMap.ext
  intro x
  change ((globalReverseMixedPairRealization q hq hq1 n hn p s 0).transport (ne_of_gt hq)
    (globalReverseMixedPairRealization q hq hq1 n hn p s r)
      ((globalReverseMixedPairRealization q hq hq1 n hn p s 0).channelProjection
        ((globalMixedPairRealization q hq hq1 n hn p s 0).transport (ne_of_gt hq)
          (globalReverseMixedPairRealization q hq hq1 n hn p s 0) x).val)).val = _
  rw [CompactHighestRealization.channelProjection_subtype,CompactHighestRealization.transport_comp]
  rfl

theorem physicalTypeIIToI_subtype_zero (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a p s : ℕ)
    (u : quantumOccupationSpace ℝ (Fin (h+2)) a ⊗[ℝ]
      (globalMixedPairRealization q hq hq1 (h+1) (by omega) p s 0).channel) :
    physicalTypeIIToI q hq hq1 (h+1) (by omega) a p s
      (TensorProduct.map LinearMap.id
        (globalMixedPairRealization q hq hq1 (h+1) (by omega) p s 0).channel.subtype u) =
      TensorProduct.map LinearMap.id (globalReverseMixedPairClebsch q hq hq1 (h+1) (by omega) p s 0) u := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u w hu hw => simp only [map_add,hu,hw]
  | tmul x y =>
    simp only [physicalTypeIIToI,TensorProduct.map_tmul,LinearMap.id_apply,
      TensorProduct.congr_tmul,LinearEquiv.refl_apply,Submodule.subtype_apply]
    rw [globalReverseMixedPairClebsch_apply,physicalMixedCommutor_zero_channel]

/-- The same second vertex (S_a,M_(p,s);S_d) used by Type II is
reused literally in the Type-I right tree, for every contraction r. -/
def globalSharedTypeIRightTree (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a p s d : ℕ) (hbal : a+p=s+d) (hs : s≤a) (r : ℕ) :=
  (TensorProduct.map (LinearMap.id : quantumOccupationSpace ℝ (Fin (h+2)) a →ₗ[ℝ] _)
    (globalReverseMixedPairClebsch q hq hq1 (h+1) (by omega) p s r)).comp
      (globalSymMixedVertex q hq hq1 h a p s d hbal hs)

theorem globalSharedTypeIRightTree_zero_highest (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a p s d : ℕ) (hbal : a+p=s+d) (hs : s≤a) :
    globalSharedTypeIRightTree q hq hq1 h a p s d hbal hs 0
      (quantumOccupationBasis (K:=ℝ) d (highestOccupation (h+1) d)) =
      (-1:ℝ)^(h*s) • (globalTypeIRightVector q hq hq1 h a p s 0 hs).val := by
  have hf:=globalTypeIIRightVertex_highest_factor q hq hq1 h a p s d hbal hs 0
  rw [globalMixedPairClebsch_zero] at hf
  unfold globalSharedTypeIRightTree
  rw [LinearMap.comp_apply,← physicalTypeIIToI_subtype_zero,hf]
  exact globalTypeIRightII_zero_comparison q hq hq1 h a p s d hbal hs

theorem globalSharedTypeIRightTree_highest (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a p s d : ℕ) (hbal : a+p=s+d) (hs : s≤a) (r : ℕ) :
    globalSharedTypeIRightTree q hq hq1 h a p s d hbal hs r
      (quantumOccupationBasis (K:=ℝ) d (highestOccupation (h+1) d)) =
      (-1:ℝ)^(h*s) • (globalTypeIRightVector q hq hq1 h a p s r hs).val := by
  unfold globalSharedTypeIRightTree
  rw [LinearMap.comp_apply,← globalReverseMixedPairClebsch_factor q hq hq1 (h+1) (by omega) p s r,
    ← tensorRight_map_comp]
  change TensorProduct.map LinearMap.id
    (globalReverseMixedPairTransfer q hq hq1 (h+1) (by omega) p s 0 r)
    (globalSharedTypeIRightTree q hq hq1 h a p s d hbal hs 0
      (quantumOccupationBasis (K:=ℝ) d (highestOccupation (h+1) d))) = _
  rw [globalSharedTypeIRightTree_zero_highest,map_smul,← globalTypeIRightVector_from_zero]

theorem globalSharedTypeIRightTree_intertwines (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a p s d : ℕ) (hbal : a+p=s+d) (hs : s≤a) (r : ℕ)
    (z : UqTypeA q (h+1)) (x : quantumOccupationSpace ℝ (Fin (h+2)) d) :
    globalSharedTypeIRightTree q hq hq1 h a p s d hbal hs r
      (typeAFiniteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) d z x) =
      typeAMixedTriple q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) a (s+r) (p+r) z
        (globalSharedTypeIRightTree q hq hq1 h a p s d hbal hs r x) := by
  unfold globalSharedTypeIRightTree
  simp only [LinearMap.comp_apply]
  rw [globalSymMixedVertex_intertwines]
  exact typeA_intertwiner_tensor q (ne_of_gt hq) (h+1) _ _ _ _ LinearMap.id _
    (fun _ _=>rfl) (globalReverseMixedPairClebsch_intertwines q hq hq1 (h+1) (by omega) p s r) z _

theorem globalSharedTypeIRightTree_isometry (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a p s d : ℕ) (hbal : a+p=s+d) (hs : s≤a) (r : ℕ)
    (x y : quantumOccupationSpace ℝ (Fin (h+2)) d) :
    physicalTripleBilin q (h+1) a (s+r) (p+r)
      (globalSharedTypeIRightTree q hq hq1 h a p s d hbal hs r x)
      (globalSharedTypeIRightTree q hq hq1 h a p s d hbal hs r y) =
      occupationCompactBilin q (h+1) d x y := by
  have he:=tensorWeightedBilin_right_carrier_isometry
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin (h+2)) a)
    ((quantumOccupationBasis (K:=ℝ) (ι:=Fin (h+2)) p).tensorProduct
      (quantumOccupationBasis (K:=ℝ) (ι:=Fin (h+2)) s))
    ((quantumOccupationBasis (K:=ℝ) (ι:=Fin (h+2)) (s+r)).tensorProduct
      (quantumOccupationBasis (K:=ℝ) (ι:=Fin (h+2)) (p+r)))
    (occupationCompactWeight q (h+1) a)
    (fun yz=>occupationCompactWeight q (h+1) p yz.1*occupationOppositeWeight q (h+1) s yz.2)
    (fun yz=>occupationOppositeWeight q (h+1) (s+r) yz.1*occupationCompactWeight q (h+1) (p+r) yz.2)
    (globalMixedPairRealization q hq hq1 (h+1) (by omega) p s 0).channel.subtype
    (globalReverseMixedPairClebsch q hq hq1 (h+1) (by omega) p s r)
    (globalReverseMixedPairClebsch_isometry q hq hq1 (h+1) (by omega) p s r)
    (globalSymMixedVertex q hq hq1 h a p s d hbal hs x)
    (globalSymMixedVertex q hq hq1 h a p s d hbal hs y)
  rw [physicalTripleBilin_tensor]
  exact he.trans (globalSymMixedVertex_isometry q hq hq1 h a p s d hbal hs x y)

end AMSPhysical
#print axioms AMSPhysical.globalSharedTypeIRightTree_highest
#print axioms AMSPhysical.globalSharedTypeIRightTree_intertwines
