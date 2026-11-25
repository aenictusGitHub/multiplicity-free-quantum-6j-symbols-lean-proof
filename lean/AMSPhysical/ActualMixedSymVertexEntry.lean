import ActualReverseMixedVertexEntry
import GlobalMixedSymHighestLine

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical

/-- The Type-I left outer vertex is an entry of the same actual-weight
table used by both inner-vertex families. Pure aliases are included. -/
theorem actualPositiveVertexTable_mixed_sym_entry (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h : ℕ) (hh : 1≤h) (p s c : ℕ) (hs : s≤c) :
    actualPositiveVertexTable (ne_of_gt hq) (amsActualBoundary q hq hq1 (h+1) (by omega))
      (actualMixedCarrier q hq hq1 (h+1) (by omega) p s).irrep
      (actualSymmetricCarrier q hq hq1 (h+1) c).irrep
      (actualSymmetricCarrier q hq hq1 (h+1) (p+c-s)).irrep =
    canonicalizeActualVertex (ne_of_gt hq)
      (actualMixedCarrier q hq hq1 (h+1) (by omega) p s)
      (actualSymmetricCarrier q hq hq1 (h+1) c)
      (actualSymmetricCarrier q hq hq1 (h+1) (p+c-s))
      (globalMixedSymVertex q hq hq1 h p s c hs) := by
  apply actualPositiveVertexTable_eq
  · rw [actualVertex_highest_finrank]
    exact globalMixedSymHighestSpace_finrank_one q hq hq1 h p s c hs
  · apply canonicalizeActualVertex_positive (ne_of_gt hq)
      (amsActualBoundary q hq hq1 (h+1) (by omega))
      (actualMixedCarrier q hq hq1 (h+1) (by omega) p s)
      (actualSymmetricCarrier q hq hq1 (h+1) c)
      (actualSymmetricCarrier q hq hq1 (h+1) (p+c-s))
      (occupationAugmentation (h+1) c)
      (amsActualBoundary_symmetric q hq hq1 (h+1) (by omega) c)
      (globalMixedSymVertex q hq hq1 h p s c hs)
    · exact globalMixedSymVertex_intertwines q hq hq1 h p s c hs
    · exact globalMixedSymVertex_highest_norm q hq hq1 h p s c hs
    · exact globalMixedSymVertex_highest_boundary_pos q hq hq1 h p s c hs

end AMSPhysical
#print axioms AMSPhysical.actualPositiveVertexTable_mixed_sym_entry
