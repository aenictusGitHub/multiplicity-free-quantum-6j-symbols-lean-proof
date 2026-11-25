import ActualAMSTableTrees

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def actualTriplePair {q : ℝ} {n : ℕ} (A B C : ActualIrrep q n) :=
  LinearMap.BilinForm.tmul (fixedActualCarrier A).frame.pairing
    (LinearMap.BilinForm.tmul (fixedActualCarrier B).frame.pairing (fixedActualCarrier C).frame.pairing)

theorem actualLeftVertexTree_highest_congr {q : ℝ} {n : ℕ} (T : ActualVertexTable q n)
    (A B C D E D' E' : ActualIrrep q n) (hD : D=D') (hE : E=E') :
    actualLeftVertexTree T A B C D E (fixedActualCarrier D).frame.highest =
      actualLeftVertexTree T A B C D' E' (fixedActualCarrier D').frame.highest := by
  subst D'
  subst E'
  rfl

theorem actualRightVertexTree_highest_congr {q : ℝ} {n : ℕ} (T : ActualVertexTable q n)
    (A B C D E D' E' : ActualIrrep q n) (hD : D=D') (hE : E=E') :
    actualRightVertexTree T A B C D E (fixedActualCarrier D).frame.highest =
      actualRightVertexTree T A B C D' E' (fixedActualCarrier D').frame.highest := by
  subst D'
  subst E'
  rfl

def actualTypeILeftHighest (q : ℝ) (hq : 0<q) (hq1 : q≠1) (h : ℕ) (hh : 1≤h)
    (l m c : ℕ) (s : QuantumCupIndex l m c) :=
  actualLeftVertexTree (amsActualVertexTable q hq hq1 (h+1) (by omega))
    (actualSymmetricCarrier q hq hq1 (h+1) l).irrep
    (actualOppositeCarrier q hq hq1 (h+1) (by omega) m).irrep
    (actualSymmetricCarrier q hq hq1 (h+1) c).irrep
    (actualSymmetricCarrier q hq hq1 (h+1) (l+c-m)).irrep
    (actualMixedCarrier q hq hq1 (h+1) (by omega) (l-s.val.val) (m-s.val.val)).irrep
    (fixedActualCarrier (actualSymmetricCarrier q hq hq1 (h+1) (l+c-m)).irrep).frame.highest

def actualTypeIRightHighest (q : ℝ) (hq : 0<q) (hq1 : q≠1) (h : ℕ) (hh : 1≤h)
    (l m c : ℕ) (t : QuantumCupIndex l m c) :=
  actualRightVertexTree (amsActualVertexTable q hq hq1 (h+1) (by omega))
    (actualSymmetricCarrier q hq hq1 (h+1) l).irrep
    (actualOppositeCarrier q hq hq1 (h+1) (by omega) m).irrep
    (actualSymmetricCarrier q hq hq1 (h+1) c).irrep
    (actualSymmetricCarrier q hq hq1 (h+1) (l+c-m)).irrep
    (actualMixedCarrier q hq hq1 (h+1) (by omega) (c-(m-t.val.val)) t.val.val).irrep
    (fixedActualCarrier (actualSymmetricCarrier q hq hq1 (h+1) (l+c-m)).irrep).frame.highest

def actualTypeIILeftHighest (q : ℝ) (hq : 0<q) (hq1 : q≠1) (h : ℕ) (hh : 1≤h)
    (a b c d : ℕ) (r : TypeIICommonIndex a b c d) :=
  actualLeftVertexTree (amsActualVertexTable q hq hq1 (h+1) (by omega))
    (actualSymmetricCarrier q hq hq1 (h+1) a).irrep (actualSymmetricCarrier q hq hq1 (h+1) b).irrep
    (actualOppositeCarrier q hq hq1 (h+1) (by omega) c).irrep (actualSymmetricCarrier q hq hq1 (h+1) d).irrep
    (nativeTypeIITwoRowCarrier q hq hq1 (h+1) (by omega) a b c d r).irrep
    (fixedActualCarrier (actualSymmetricCarrier q hq hq1 (h+1) d).irrep).frame.highest

def actualTypeIIRightHighest (q : ℝ) (hq : 0<q) (hq1 : q≠1) (h : ℕ) (hh : 1≤h)
    (a b c d : ℕ) (t : QuantumCupIndex a c b) :=
  actualRightVertexTree (amsActualVertexTable q hq hq1 (h+1) (by omega))
    (actualSymmetricCarrier q hq hq1 (h+1) a).irrep (actualSymmetricCarrier q hq hq1 (h+1) b).irrep
    (actualOppositeCarrier q hq hq1 (h+1) (by omega) c).irrep (actualSymmetricCarrier q hq hq1 (h+1) d).irrep
    (actualMixedCarrier q hq hq1 (h+1) (by omega) (b-(c-t.val.val)) t.val.val).irrep
    (fixedActualCarrier (actualSymmetricCarrier q hq hq1 (h+1) d).irrep).frame.highest

end AMSPhysical
