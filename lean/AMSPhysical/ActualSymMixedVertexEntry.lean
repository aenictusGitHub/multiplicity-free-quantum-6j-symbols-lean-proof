import ActualMixedSymVertexEntry
import GlobalSymMixedHighestLine

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical

theorem actualPositiveVertexTable_sym_mixed_entry (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h : ℕ) (hh : 1≤h) (a p s d : ℕ) (hbal : a+p=s+d) (hs : s≤a) :
    actualPositiveVertexTable (ne_of_gt hq) (amsActualBoundary q hq hq1 (h+1) (by omega))
      (actualSymmetricCarrier q hq hq1 (h+1) a).irrep
      (actualMixedCarrier q hq hq1 (h+1) (by omega) p s).irrep
      (actualSymmetricCarrier q hq hq1 (h+1) d).irrep =
    canonicalizeActualVertex (ne_of_gt hq)
      (actualSymmetricCarrier q hq hq1 (h+1) a)
      (actualMixedCarrier q hq hq1 (h+1) (by omega) p s)
      (actualSymmetricCarrier q hq hq1 (h+1) d)
      (globalSymMixedVertex q hq hq1 h a p s d hbal hs) := by
  apply actualPositiveVertexTable_eq
  · rw [actualVertex_highest_finrank]
    have hd : d=a+p-s := by omega
    subst d
    exact globalSymMixedHighestSpace_finrank_one q hq hq1 h a p s hs
  · apply canonicalizeActualVertex_positive (ne_of_gt hq)
      (amsActualBoundary q hq hq1 (h+1) (by omega))
      (actualSymmetricCarrier q hq hq1 (h+1) a)
      (actualMixedCarrier q hq hq1 (h+1) (by omega) p s)
      (actualSymmetricCarrier q hq hq1 (h+1) d)
      ((amsActualBoundary q hq hq1 (h+1) (by omega)
        (actualMixedCarrier q hq hq1 (h+1) (by omega) p s).irrep).comp
        ((actualMixedCarrier q hq hq1 (h+1) (by omega) p s).mapTo (ne_of_gt hq)
          (fixedActualCarrier (actualMixedCarrier q hq hq1 (h+1) (by omega) p s).irrep)))
      (by intro v;rfl) (globalSymMixedVertex q hq hq1 h a p s d hbal hs)
    · exact globalSymMixedVertex_intertwines q hq hq1 h a p s d hbal hs
    · exact globalSymMixedVertex_highest_norm q hq hq1 h a p s d hbal hs
    · exact globalSymMixedVertex_actual_boundary_pos q hq hq1 h hh a p s d hbal hs

end AMSPhysical
#print axioms AMSPhysical.actualPositiveVertexTable_sym_mixed_entry
