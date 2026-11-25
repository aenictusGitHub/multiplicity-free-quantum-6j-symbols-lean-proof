import SharedActualAMSUnitary
import ActualTreeFromEntries
import AMSSharedNativeTreePhases

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical

theorem actualAMSTable_TypeI_left_tree (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h : ℕ) (hh : 1≤h) (p s c : ℕ) (hs : s≤c) (r : ℕ) :
    actualLeftVertexTree (amsActualVertexTable q hq hq1 (h+1) (by omega))
      (actualSymmetricCarrier q hq hq1 (h+1) (p+r)).irrep
      (actualOppositeCarrier q hq hq1 (h+1) (by omega) (s+r)).irrep
      (actualSymmetricCarrier q hq hq1 (h+1) c).irrep
      (actualSymmetricCarrier q hq hq1 (h+1) (p+c-s)).irrep
      (actualMixedCarrier q hq hq1 (h+1) (by omega) p s).irrep
      (fixedActualCarrier (actualSymmetricCarrier q hq hq1 (h+1) (p+c-s)).irrep).frame.highest =
    canonicalizeActualTriple (ne_of_gt hq)
      (actualSymmetricCarrier q hq hq1 (h+1) (p+r))
      (actualOppositeCarrier q hq hq1 (h+1) (by omega) (s+r))
      (actualSymmetricCarrier q hq hq1 (h+1) c) (globalTypeILeftVector q hq hq1 h p s c r hs).val := by
  have H:=amsActualVertexTable_shared q hq hq1 h hh
  have hF:= (H.forward p s r).trans (canonicalizeActualVertex_smul (ne_of_gt hq)
    (actualSymmetricCarrier q hq hq1 (h+1) (p+r))
    (actualOppositeCarrier q hq hq1 (h+1) (by omega) (s+r))
    (actualMixedCarrier q hq hq1 (h+1) (by omega) p s)
    (globalMixedPairClebsch q hq hq1 (h+1) (by omega) p s r) ((-1:ℝ)^(h*r))).symm
  have hG:=H.mixed_sym p s c hs
  simp only [one_smul] at hG
  have hTree:=actualLeftVertexTree_of_entries (ne_of_gt hq) _
    (actualSymmetricCarrier q hq hq1 (h+1) (p+r))
    (actualOppositeCarrier q hq hq1 (h+1) (by omega) (s+r))
    (actualSymmetricCarrier q hq hq1 (h+1) c)
    (actualSymmetricCarrier q hq hq1 (h+1) (p+c-s))
    (actualMixedCarrier q hq hq1 (h+1) (by omega) p s)
    (globalAMSMixedIn q hq hq1 h p s r) (globalMixedSymVertex q hq hq1 h p s c hs) hF hG
  refine hTree.trans ?_
  apply congrArg (canonicalizeActualTriple (ne_of_gt hq)
    (actualSymmetricCarrier q hq hq1 (h+1) (p+r))
    (actualOppositeCarrier q hq hq1 (h+1) (by omega) (s+r)) (actualSymmetricCarrier q hq hq1 (h+1) c))
  exact amsSharedNative_TypeI_left_highest q hq hq1 h p s c hs r

theorem actualAMSTable_TypeI_right_tree (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h : ℕ) (hh : 1≤h) (a p s d : ℕ) (hbal : a+p=s+d) (hs : s≤a) (r : ℕ) :
    actualRightVertexTree (amsActualVertexTable q hq hq1 (h+1) (by omega))
      (actualSymmetricCarrier q hq hq1 (h+1) a).irrep
      (actualOppositeCarrier q hq hq1 (h+1) (by omega) (s+r)).irrep
      (actualSymmetricCarrier q hq hq1 (h+1) (p+r)).irrep
      (actualSymmetricCarrier q hq hq1 (h+1) d).irrep
      (actualMixedCarrier q hq hq1 (h+1) (by omega) p s).irrep
      (fixedActualCarrier (actualSymmetricCarrier q hq hq1 (h+1) d).irrep).frame.highest =
    canonicalizeActualTriple (ne_of_gt hq)
      (actualSymmetricCarrier q hq hq1 (h+1) a)
      (actualOppositeCarrier q hq hq1 (h+1) (by omega) (s+r))
      (actualSymmetricCarrier q hq hq1 (h+1) (p+r)) (globalTypeIRightVector q hq hq1 h a p s r hs).val := by
  have H:=amsActualVertexTable_shared q hq hq1 h hh
  have hF:=H.reverse p s r
  simp only [one_smul] at hF
  have hG:=(H.sym_mixed a p s d hbal hs).trans (canonicalizeActualVertex_smul (ne_of_gt hq)
    (actualSymmetricCarrier q hq hq1 (h+1) a) (actualMixedCarrier q hq hq1 (h+1) (by omega) p s)
    (actualSymmetricCarrier q hq hq1 (h+1) d)
    (globalSymMixedVertex q hq hq1 h a p s d hbal hs) ((-1:ℝ)^(h*s))).symm
  have hTree:=actualRightVertexTree_of_entries (ne_of_gt hq) _
    (actualSymmetricCarrier q hq hq1 (h+1) a)
    (actualOppositeCarrier q hq hq1 (h+1) (by omega) (s+r))
    (actualSymmetricCarrier q hq hq1 (h+1) (p+r)) (actualSymmetricCarrier q hq hq1 (h+1) d)
    (actualMixedCarrier q hq hq1 (h+1) (by omega) p s)
    (globalReverseMixedPairClebsch q hq hq1 (h+1) (by omega) p s r)
    ((-1:ℝ)^(h*s) • globalSymMixedVertex q hq hq1 h a p s d hbal hs) hF hG
  refine hTree.trans ?_
  apply congrArg (canonicalizeActualTriple (ne_of_gt hq)
    (actualSymmetricCarrier q hq hq1 (h+1) a)
    (actualOppositeCarrier q hq hq1 (h+1) (by omega) (s+r))
    (actualSymmetricCarrier q hq hq1 (h+1) (p+r)))
  exact amsSharedNative_TypeI_right_highest q hq hq1 h a p s d hbal hs r

theorem actualAMSTable_TypeII_left_tree (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h : ℕ) (hh : 1≤h) (a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d) :
    actualLeftVertexTree (amsActualVertexTable q hq hq1 (h+1) (by omega))
      (actualSymmetricCarrier q hq hq1 (h+1) a).irrep (actualSymmetricCarrier q hq hq1 (h+1) b).irrep
      (actualOppositeCarrier q hq hq1 (h+1) (by omega) c).irrep (actualSymmetricCarrier q hq hq1 (h+1) d).irrep
      (nativeTypeIITwoRowCarrier q hq hq1 (h+1) (by omega) a b c d r).irrep
      (fixedActualCarrier (actualSymmetricCarrier q hq hq1 (h+1) d).irrep).frame.highest =
    (-1:ℝ)^(h*c) • canonicalizeActualTriple (ne_of_gt hq)
      (actualSymmetricCarrier q hq hq1 (h+1) a) (actualSymmetricCarrier q hq hq1 (h+1) b)
      (actualOppositeCarrier q hq hq1 (h+1) (by omega) c)
      (physicalTypeIICalibratedLeft q hq hq1 h a b c d hbal r).val := by
  have H:=amsActualVertexTable_shared q hq hq1 h hh
  have hF:=H.two_row a b c d r
  simp only [one_smul] at hF
  have hG:=(H.two_row_opp a b c d hbal r).trans (canonicalizeActualVertex_smul (ne_of_gt hq)
    (nativeTypeIITwoRowCarrier q hq hq1 (h+1) (by omega) a b c d r)
    (actualOppositeCarrier q hq hq1 (h+1) (by omega) c) (actualSymmetricCarrier q hq hq1 (h+1) d)
    (nativeTypeIIOuterVertex q hq hq1 (h+1) (by omega) a b c d hbal r) ((-1:ℝ)^(h*c))).symm
  have hTree:=actualLeftVertexTree_of_entries (ne_of_gt hq) _
    (actualSymmetricCarrier q hq hq1 (h+1) a) (actualSymmetricCarrier q hq hq1 (h+1) b)
    (actualOppositeCarrier q hq hq1 (h+1) (by omega) c) (actualSymmetricCarrier q hq hq1 (h+1) d)
    (nativeTypeIITwoRowCarrier q hq hq1 (h+1) (by omega) a b c d r)
    (typeIILeftTarget q hq hq1 (h+1) (by omega) a b c d r).channel.subtype
    ((-1:ℝ)^(h*c) • nativeTypeIIOuterVertex q hq hq1 (h+1) (by omega) a b c d hbal r) hF hG
  have hNative:=congrArg (canonicalizeActualTriple (ne_of_gt hq)
    (actualSymmetricCarrier q hq hq1 (h+1) a) (actualSymmetricCarrier q hq hq1 (h+1) b)
    (actualOppositeCarrier q hq hq1 (h+1) (by omega) c))
    (amsSharedNative_TypeII_left_highest q hq hq1 h a b c d hbal r)
  simp only [map_smul] at hNative
  exact hTree.trans hNative

theorem actualAMSTable_TypeII_right_tree (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h : ℕ) (hh : 1≤h) (a p s d : ℕ) (hbal : a+p=s+d) (hs : s≤a) (r : ℕ) :
    actualRightVertexTree (amsActualVertexTable q hq hq1 (h+1) (by omega))
      (actualSymmetricCarrier q hq hq1 (h+1) a).irrep
      (actualSymmetricCarrier q hq hq1 (h+1) (p+r)).irrep
      (actualOppositeCarrier q hq hq1 (h+1) (by omega) (s+r)).irrep
      (actualSymmetricCarrier q hq hq1 (h+1) d).irrep
      (actualMixedCarrier q hq hq1 (h+1) (by omega) p s).irrep
      (fixedActualCarrier (actualSymmetricCarrier q hq hq1 (h+1) d).irrep).frame.highest =
    (-1:ℝ)^(h*(s+r)) • canonicalizeActualTriple (ne_of_gt hq)
      (actualSymmetricCarrier q hq hq1 (h+1) a) (actualSymmetricCarrier q hq hq1 (h+1) (p+r))
      (actualOppositeCarrier q hq hq1 (h+1) (by omega) (s+r))
      (globalTypeIIRightVector q hq hq1 h a p s d hbal hs r).val := by
  have H:=amsActualVertexTable_shared q hq hq1 h hh
  have hF:=(H.forward p s r).trans (canonicalizeActualVertex_smul (ne_of_gt hq)
    (actualSymmetricCarrier q hq hq1 (h+1) (p+r))
    (actualOppositeCarrier q hq hq1 (h+1) (by omega) (s+r))
    (actualMixedCarrier q hq hq1 (h+1) (by omega) p s)
    (globalMixedPairClebsch q hq hq1 (h+1) (by omega) p s r) ((-1:ℝ)^(h*r))).symm
  have hG:=(H.sym_mixed a p s d hbal hs).trans (canonicalizeActualVertex_smul (ne_of_gt hq)
    (actualSymmetricCarrier q hq hq1 (h+1) a) (actualMixedCarrier q hq hq1 (h+1) (by omega) p s)
    (actualSymmetricCarrier q hq hq1 (h+1) d) (globalSymMixedVertex q hq hq1 h a p s d hbal hs)
    ((-1:ℝ)^(h*s))).symm
  have hTree:=actualRightVertexTree_of_entries (ne_of_gt hq) _
    (actualSymmetricCarrier q hq hq1 (h+1) a) (actualSymmetricCarrier q hq hq1 (h+1) (p+r))
    (actualOppositeCarrier q hq hq1 (h+1) (by omega) (s+r)) (actualSymmetricCarrier q hq hq1 (h+1) d)
    (actualMixedCarrier q hq hq1 (h+1) (by omega) p s) (globalAMSMixedIn q hq hq1 h p s r)
    ((-1:ℝ)^(h*s) • globalSymMixedVertex q hq hq1 h a p s d hbal hs) hF hG
  have hNative:=congrArg (canonicalizeActualTriple (ne_of_gt hq)
    (actualSymmetricCarrier q hq hq1 (h+1) a) (actualSymmetricCarrier q hq hq1 (h+1) (p+r))
    (actualOppositeCarrier q hq hq1 (h+1) (by omega) (s+r)))
    (amsSharedNative_TypeII_right_highest q hq hq1 h a p s d hbal hs r)
  simp only [map_smul] at hNative
  exact hTree.trans hNative

end AMSPhysical
#print axioms AMSPhysical.actualAMSTable_TypeI_left_tree
#print axioms AMSPhysical.actualAMSTable_TypeI_right_tree
#print axioms AMSPhysical.actualAMSTable_TypeII_left_tree
#print axioms AMSPhysical.actualAMSTable_TypeII_right_tree
