import NativeTypeIIVertices

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem nativeTypeIITwoRowOut_bend_boundary (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d) :
    occupationAugmentation n c (tensorFirstFunctional
      ((nativeTypeIITwoRowCarrier q hq hq1 n hn a b c d r).frame.pairing
        (nativeTypeIITwoRowCarrier q hq hq1 n hn a b c d r).frame.highest)
      (bendRight (nativeTypeIITwoRowOut q hq hq1 n hn a b c d hbal r)
        (symmetricCoevaluation q n c)
        (quantumOccupationBasis (K:=ℝ) d (highestOccupation n d)))) =
      (-1:ℝ)^r.val*(Real.sqrt (couplingNormClosed q (d-r.val) (c-r.val) r.val))⁻¹ := by
  classical
  have hd : r.val≤d := by have hr:=r.isLt;omega
  have hc : r.val≤c := by have hr:=r.isLt;omega
  rw [symmetricCoevaluation_diagonal,bendRight_diagonal]
  simp only [map_sum,map_smul,tensorFirstFunctional_tmul,smul_smul,
    occupationAugmentation_basis,smul_eq_mul,mul_one,
    nativeTypeIITwoRowOut_highest_functional,twoRowHighest_metric_boundary q hq]
  rw [Finset.sum_eq_single (twoVertexOccupation n hn c ⟨r.val,by omega⟩)]
  · rw [if_pos rfl]
    have hW:=ne_of_gt (occupationCompactWeight_pos q hq n c (twoVertexOccupation n hn c ⟨r.val,by omega⟩))
    rw [occupationDualSign_twoVertex]
    simp only [Fin.val_mk,mul_one]
    field_simp [hW]
  · intro x hx hxy
    rw [if_neg (Ne.symm hxy),mul_zero,mul_zero]
  · simp

theorem nativeTypeIIOuterVertex_boundary_pos (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d) :
    0 < occupationAugmentation n c (tensorFirstFunctional
      ((nativeTypeIITwoRowCarrier q hq hq1 n hn a b c d r).frame.pairing
        (nativeTypeIITwoRowCarrier q hq hq1 n hn a b c d r).frame.highest)
      (nativeTypeIIOuterVertex q hq hq1 n hn a b c d hbal r
        (quantumOccupationBasis (K:=ℝ) d (highestOccupation n d)))) := by
  unfold nativeTypeIIOuterVertex
  simp only [LinearMap.smul_apply,map_smul,smul_eq_mul]
  rw [nativeTypeIITwoRowOut_bend_boundary]
  have hd : r.val≤d := by have hr:=r.isLt;omega
  have hc : r.val≤c := by have hr:=r.isLt;omega
  have hp:=globalTypeIILeftVertex_highest_boundary_pos q hq hq1 n hn (c+d) r.val (by omega)
    d c (by omega) hd hc
  simp only [LinearMap.smul_apply,map_smul,smul_eq_mul] at hp
  rw [globalTwoRowOut_bend_highest_boundary] at hp
  exact hp

end AMSPhysical
#print axioms AMSPhysical.nativeTypeIIOuterVertex_boundary_pos
