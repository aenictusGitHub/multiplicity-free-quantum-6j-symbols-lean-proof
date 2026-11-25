import NativeTypeIIOuterHighestLine

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical

/-- The last outer role is an entry of the one actual-weight table.
Its native carrier can be any two-row realization; the canonical table
index retains only the actual Dynkin weight. -/
theorem actualPositiveVertexTable_twoRow_outer_entry (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h : ℕ) (hh : 1≤h) (a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d) :
    actualPositiveVertexTable (ne_of_gt hq) (amsActualBoundary q hq hq1 (h+1) (by omega))
      (nativeTypeIITwoRowCarrier q hq hq1 (h+1) (by omega) a b c d r).irrep
      (actualOppositeCarrier q hq hq1 (h+1) (by omega) c).irrep
      (actualSymmetricCarrier q hq hq1 (h+1) d).irrep =
    canonicalizeActualVertex (ne_of_gt hq)
      (nativeTypeIITwoRowCarrier q hq hq1 (h+1) (by omega) a b c d r)
      (actualOppositeCarrier q hq hq1 (h+1) (by omega) c)
      (actualSymmetricCarrier q hq hq1 (h+1) d)
      (nativeTypeIIOuterVertex q hq hq1 (h+1) (by omega) a b c d hbal r) := by
  apply actualPositiveVertexTable_eq
  · rw [actualVertex_highest_finrank]
    exact nativeTypeIIOuterHighestSpace_finrank_one q hq hq1 h a b c d hbal r
  · apply canonicalizeActualVertex_positive (ne_of_gt hq)
      (amsActualBoundary q hq hq1 (h+1) (by omega))
      (nativeTypeIITwoRowCarrier q hq hq1 (h+1) (by omega) a b c d r)
      (actualOppositeCarrier q hq hq1 (h+1) (by omega) c)
      (actualSymmetricCarrier q hq hq1 (h+1) d)
      (occupationAugmentation (h+1) c)
      (amsActualBoundary_opposite q hq hq1 (h+1) (by omega) c)
      (nativeTypeIIOuterVertex q hq hq1 (h+1) (by omega) a b c d hbal r)
    · exact nativeTypeIIOuterVertex_intertwines q hq hq1 (h+1) (by omega) a b c d hbal r
    · exact nativeTypeIIOuterVertex_highest_norm q hq hq1 h a b c d hbal r
    · exact nativeTypeIIOuterVertex_boundary_pos q hq hq1 (h+1) (by omega) a b c d hbal r

end AMSPhysical
#print axioms AMSPhysical.actualPositiveVertexTable_twoRow_outer_entry
