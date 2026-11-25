import TwoRowOuterHighestFunctional

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem occupationDualSign_twoVertex (n : ℕ) (hn : 0<n) (L : ℕ) (k : Fin (L+1)) :
    occupationDualSign n L (twoVertexOccupation n hn L k)=(-1:ℝ)^k.val := by
  have he : occupationHeightZ n L (twoVertexOccupation n hn L k)=(k.val:ℤ) := by
    simp [occupationHeightZ,latticePairing,twoVertexOccupation,Pi.single_apply,
      mul_add,Finset.sum_add_distrib,secondVertex]
  rw [occupationDualSign,he,zpow_natCast]

theorem globalTwoRowOut_bend_highest_boundary (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (S r : ℕ) (hr : 2*r≤S)
    (d c : ℕ) (hS : d+c=S) (hd : r≤d) (hc : r≤c) :
    occupationAugmentation n c (tensorFirstFunctional
      ((actualTwoRowCarrier q hq hq1 n hn S r hr).frame.pairing
        (actualTwoRowCarrier q hq hq1 n hn S r hr).frame.highest)
      (bendRight (globalTwoRowOut q hq hq1 n hn S r hr d c hS hd hc)
        (symmetricCoevaluation q n c)
        (quantumOccupationBasis (K:=ℝ) d (highestOccupation n d)))) =
      (-1:ℝ)^r*(Real.sqrt (couplingNormClosed q (d-r) (c-r) r))⁻¹ := by
  classical
  rw [symmetricCoevaluation_diagonal,bendRight_diagonal]
  simp only [map_sum,map_smul,tensorFirstFunctional_tmul,smul_smul,
    occupationAugmentation_basis,smul_eq_mul,mul_one,
    globalTwoRowOut_highest_functional,twoRowHighest_metric_boundary q hq]
  rw [Finset.sum_eq_single (twoVertexOccupation n hn c ⟨r,by omega⟩)]
  · rw [if_pos rfl]
    have hW:=ne_of_gt (occupationCompactWeight_pos q hq n c (twoVertexOccupation n hn c ⟨r,by omega⟩))
    rw [occupationDualSign_twoVertex]
    simp only [Fin.val_mk,mul_one]
    field_simp [hW]
  · intro x hx hxy
    rw [if_neg (Ne.symm hxy),mul_zero,mul_zero]
  · simp

theorem globalTypeIILeftVertex_highest_boundary_pos (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (S r : ℕ) (hr : 2*r≤S)
    (d c : ℕ) (hS : d+c=S) (hd : r≤d) (hc : r≤c) :
    0 < occupationAugmentation n c (tensorFirstFunctional
      ((actualTwoRowCarrier q hq hq1 n hn S r hr).frame.pairing
        (actualTwoRowCarrier q hq hq1 n hn S r hr).frame.highest)
      ((globalTypeIILeftVertexScale q hq hq1 n hn S r d •
        bendRight (globalTwoRowOut q hq hq1 n hn S r hr d c hS hd hc) (symmetricCoevaluation q n c))
        (quantumOccupationBasis (K:=ℝ) d (highestOccupation n d)))) := by
  simp only [LinearMap.smul_apply,map_smul,smul_eq_mul]
  rw [globalTwoRowOut_bend_highest_boundary]
  unfold globalTypeIILeftVertexScale
  have hsgn : (-1:ℝ)^r*(-1:ℝ)^r=1 := by rw [← mul_pow];norm_num
  have hp : 0 < (Real.sqrt
      (twoRowIrrepQuantumDimension q hq hq1 n hn (S-2*r) r / symmetricQuantumDimension q n d))⁻¹ := by
    have hD : 0<symmetricQuantumDimension q n d := by
      unfold symmetricQuantumDimension
      exact div_pos (qfactorial_pos q hq (n+d))
        (mul_pos (qfactorial_pos q hq n) (qfactorial_pos q hq d))
    exact inv_pos.mpr (Real.sqrt_pos.mpr (div_pos
      (twoRowIrrepQuantumDimension_pos q hq hq1 n hn _ _) hD))
  have hN := inv_pos.mpr (Real.sqrt_pos.mpr (couplingNormClosed_pos q hq (d-r) (c-r) r))
  have he : ((-1:ℝ)^r * (Real.sqrt
      (twoRowIrrepQuantumDimension q hq hq1 n hn (S-2*r) r / symmetricQuantumDimension q n d))⁻¹) *
      ((-1:ℝ)^r*(Real.sqrt (couplingNormClosed q (d-r) (c-r) r))⁻¹) =
      (Real.sqrt (twoRowIrrepQuantumDimension q hq hq1 n hn (S-2*r) r / symmetricQuantumDimension q n d))⁻¹ *
        (Real.sqrt (couplingNormClosed q (d-r) (c-r) r))⁻¹ := by
    calc
      _ = ((-1:ℝ)^r*(-1:ℝ)^r) *
          ((Real.sqrt (twoRowIrrepQuantumDimension q hq hq1 n hn (S-2*r) r / symmetricQuantumDimension q n d))⁻¹ *
            (Real.sqrt (couplingNormClosed q (d-r) (c-r) r))⁻¹) := by ring
      _ = _ := by rw [hsgn,one_mul]
  rw [he]
  exact mul_pos hp hN

end AMSPhysical
#print axioms AMSPhysical.globalTypeIILeftVertex_highest_boundary_pos
