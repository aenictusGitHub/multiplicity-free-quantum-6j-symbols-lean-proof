import NativeTypeIIVertices

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

/-- The same actual table entry is obtained in every native two-row pair;
the source carrier is transported once to its fixed actual Dynkin object. -/
theorem actualPositiveVertexTable_native_twoRow_entry (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 2≤n) (a b c d : ℕ) (r : TypeIICommonIndex a b c d) :
    actualPositiveVertexTable (ne_of_gt hq) (amsActualBoundary q hq hq1 n hn)
      (actualSymmetricCarrier q hq hq1 n a).irrep (actualSymmetricCarrier q hq hq1 n b).irrep
      (nativeTypeIITwoRowCarrier q hq hq1 n (by omega) a b c d r).irrep =
    canonicalizeActualVertex (ne_of_gt hq)
      (actualSymmetricCarrier q hq hq1 n a) (actualSymmetricCarrier q hq hq1 n b)
      (nativeTypeIITwoRowCarrier q hq hq1 n (by omega) a b c d r)
      (typeIILeftTarget q hq hq1 n (by omega) a b c d r).channel.subtype := by
  have ha : r.val≤a := by have hr:=r.isLt;omega
  have hb : r.val≤b := by have hr:=r.isLt;omega
  apply actualPositiveVertexTable_eq
  · rw [actualVertex_highest_finrank]
    change Module.finrank ℝ (typeAHighestSpace
      (V:=quantumOccupationSpace ℝ (Fin (n+1)) a ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) b)
      q n (typeASymmetricTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b)
      (twoRowHighestWeight n (by omega) (a+b) 0 r.val))=1
    rw [← twoRowHighestWeight_total n (by omega) (a+b) a b r.val rfl]
    exact twoRowHighestSpace_finrank_one q hq hq1 n (by omega) a b ⟨r.val,by omega⟩
  · apply canonicalizeActualVertex_positive (ne_of_gt hq) (amsActualBoundary q hq hq1 n hn)
      (actualSymmetricCarrier q hq hq1 n a) (actualSymmetricCarrier q hq hq1 n b)
      (nativeTypeIITwoRowCarrier q hq hq1 n (by omega) a b c d r)
      (occupationAugmentation n b) (amsActualBoundary_symmetric q hq hq1 n hn b)
      (typeIILeftTarget q hq hq1 n (by omega) a b c d r).channel.subtype
    · intro z v;rfl
    · change LinearMap.BilinForm.tmul (occupationCompactBilin q n a) (occupationCompactBilin q n b)
        (normalizedTwoRowHighest q n (by omega) a b r.val ha hb)
        (normalizedTwoRowHighest q n (by omega) a b r.val ha hb)=1
      rw [← symmetricTensorBilin_eq_intrinsic]
      exact normalizedTwoRowHighest_norm_one q hq hq1 n (by omega) a b r.val ha hb
    · have he : (actualSymmetricCarrier q hq hq1 n a).frame.pairing
          (actualSymmetricCarrier q hq hq1 n a).frame.highest =
          occupationCoordinate n a (highestOccupation n a) := by
        apply LinearMap.ext
        exact symmetric_highest_functional_coordinate q hq n a
      rw [he]
      exact normalizedTwoRowHighest_augmentation_pos q hq n (by omega) a b r.val ha hb

end AMSPhysical
#print axioms AMSPhysical.actualPositiveVertexTable_native_twoRow_entry
