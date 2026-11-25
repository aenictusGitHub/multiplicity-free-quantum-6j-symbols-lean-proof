import NativeTypeIIOuterBoundary
import ActualNativeTwoRowEntry

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem nativeTypeIITwoRowInclusion_injective (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (a b c d : ℕ) (r : TypeIICommonIndex a b c d) :
    Function.Injective (nativeTypeIITwoRowInclusion q hq hq1 n hn a b c d r) :=
  (TensorProduct.assoc ℝ _ _ _).injective.comp
    (TensorProduct.map_injective_of_flat_flat _ _ Subtype.val_injective Function.injective_id)

theorem nativeTypeIITwoRowInclusion_intertwines (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (a b c d : ℕ) (r : TypeIICommonIndex a b c d) (z : UqTypeA q n)
    (v : (typeIILeftTarget q hq hq1 n hn a b c d r).channel ⊗[ℝ]
      quantumOccupationSpace ℝ (Fin (n+1)) c) :
    nativeTypeIITwoRowInclusion q hq hq1 n hn a b c d r
      (typeATensorRepresentation q (ne_of_gt hq) n
        (typeIILeftTarget q hq hq1 n hn a b c d r).channelAction
        (typeAOppositeSymmetricRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n c) z v)=
      typeATypeIITriple q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c z
        (nativeTypeIITwoRowInclusion q hq hq1 n hn a b c d r v) := by
  have hT:=typeA_intertwiner_tensor q (ne_of_gt hq) n
    (typeIILeftTarget q hq hq1 n hn a b c d r).channelAction
    (typeAOppositeSymmetricRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n c)
    (typeASymmetricTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b)
    (typeAOppositeSymmetricRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n c)
    (typeIILeftTarget q hq hq1 n hn a b c d r).channel.subtype LinearMap.id
    (by intro z x;rfl) (by intro z x;rfl) z v
  refine (congrArg (TensorProduct.assoc ℝ
    (quantumOccupationSpace ℝ (Fin (n+1)) a)
    (quantumOccupationSpace ℝ (Fin (n+1)) b)
    (quantumOccupationSpace ℝ (Fin (n+1)) c)) hT).trans ?_
  exact typeA_associator_intertwines q (ne_of_gt hq) n
    (typeAFiniteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a)
    (typeAFiniteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n b)
    (typeAOppositeSymmetricRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n c) z _

theorem nativeTypeIITwoRowInclusion_isometry (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (a b c d : ℕ) (r : TypeIICommonIndex a b c d)
    (v w : (typeIILeftTarget q hq hq1 n hn a b c d r).channel ⊗[ℝ]
      quantumOccupationSpace ℝ (Fin (n+1)) c) :
    physicalTypeIITripleBilin q n a b c (nativeTypeIITwoRowInclusion q hq hq1 n hn a b c d r v)
      (nativeTypeIITwoRowInclusion q hq hq1 n hn a b c d r w)=
      LinearMap.BilinForm.tmul (typeIILeftTarget q hq hq1 n hn a b c d r).channelPair
        (occupationOppositeBilin q n c) v w := by
  unfold nativeTypeIITwoRowInclusion
  simp only [LinearMap.comp_apply,LinearEquiv.coe_coe]
  rw [physicalTypeIITripleBilin_assoc,tensorWeightedBilin_eq_intrinsic]
  change LinearMap.BilinForm.tmul (symmetricTensorBilin q n a b) (occupationOppositeBilin q n c)
    (TensorProduct.map (typeIILeftTarget q hq hq1 n hn a b c d r).channel.subtype LinearMap.id v)
    (TensorProduct.map (typeIILeftTarget q hq hq1 n hn a b c d r).channel.subtype LinearMap.id w)=_
  exact tensorBilin_isometry (typeIILeftTarget q hq hq1 n hn a b c d r).channelPair
    (occupationOppositeBilin q n c) (symmetricTensorBilin q n a b) (occupationOppositeBilin q n c)
    (typeIILeftTarget q hq hq1 n hn a b c d r).channel.subtype LinearMap.id
    (by intro x y;rfl) (by intro x y;rfl) v w

theorem nativeTypeIIOuterVertex_calibrated_highest (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d) :
    nativeTypeIITwoRowInclusion q hq hq1 (h+1) (by omega) a b c d r
      (nativeTypeIIOuterVertex q hq hq1 (h+1) (by omega) a b c d hbal r
        (quantumOccupationBasis (K:=ℝ) d (highestOccupation (h+1) d))) =
      (physicalTypeIICalibratedLeft q hq hq1 h a b c d hbal r).val := by
  have hTree:=DFunLike.congr_fun (nativeTypeIITwoRowOut_tree_factor q hq hq1 (h+1) (by omega)
    a b c d hbal r) (quantumOccupationBasis (K:=ℝ) d (highestOccupation (h+1) d))
  change nativeTypeIITwoRowInclusion q hq hq1 (h+1) (by omega) a b c d r
    (bendRight (nativeTypeIITwoRowOut q hq hq1 (h+1) (by omega) a b c d hbal r)
      (symmetricCoevaluation q (h+1) c)
      (quantumOccupationBasis (K:=ℝ) d (highestOccupation (h+1) d))) =
      (physicalTypeIILeftHighest q hq hq1 (h+1) (by omega) a b c d hbal r).val at hTree
  unfold nativeTypeIIOuterVertex
  rw [LinearMap.smul_apply,map_smul]
  exact (congrArg (fun v=>globalTypeIILeftVertexScale q hq hq1 (h+1) (by omega) (c+d) r.val d • v) hTree).trans
    (physicalTypeIICalibratedLeft_global_scale q hq hq1 h a b c d hbal r).symm

theorem nativeTypeIIOuterVertex_highest_norm (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d) :
    LinearMap.BilinForm.tmul (typeIILeftTarget q hq hq1 (h+1) (by omega) a b c d r).channelPair
      (occupationOppositeBilin q (h+1) c)
      (nativeTypeIIOuterVertex q hq hq1 (h+1) (by omega) a b c d hbal r
        (quantumOccupationBasis (K:=ℝ) d (highestOccupation (h+1) d)))
      (nativeTypeIIOuterVertex q hq hq1 (h+1) (by omega) a b c d hbal r
        (quantumOccupationBasis (K:=ℝ) d (highestOccupation (h+1) d)))=1 := by
  have hIso:=nativeTypeIITwoRowInclusion_isometry q hq hq1 (h+1) (by omega) a b c d r
    (nativeTypeIIOuterVertex q hq hq1 (h+1) (by omega) a b c d hbal r
      (quantumOccupationBasis (K:=ℝ) d (highestOccupation (h+1) d)))
    (nativeTypeIIOuterVertex q hq hq1 (h+1) (by omega) a b c d hbal r
      (quantumOccupationBasis (K:=ℝ) d (highestOccupation (h+1) d)))
  exact hIso.symm.trans ((congrArg (fun v=>physicalTypeIITripleBilin q (h+1) a b c v v)
    (nativeTypeIIOuterVertex_calibrated_highest q hq hq1 h a b c d hbal r)).trans
      (physicalTypeIICalibratedLeft_unit q hq hq1 h a b c d hbal r))

end AMSPhysical
#print axioms AMSPhysical.nativeTypeIIOuterVertex_calibrated_highest
#print axioms AMSPhysical.nativeTypeIIOuterVertex_highest_norm
