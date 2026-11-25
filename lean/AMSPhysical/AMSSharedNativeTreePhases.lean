import ActualVertexTreeCoherence
import NativeTypeIIInclusion

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem amsSharedNative_TypeI_left_highest (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h p s c : ℕ) (hs : s≤c) (r : ℕ) :
    (TensorProduct.assoc ℝ (quantumOccupationSpace ℝ (Fin (h+2)) (p+r))
      (quantumOccupationSpace ℝ (Fin (h+2)) (s+r)) (quantumOccupationSpace ℝ (Fin (h+2)) c))
      (TensorProduct.map (globalAMSMixedIn q hq hq1 h p s r) LinearMap.id
        (globalMixedSymVertex q hq hq1 h p s c hs
          (quantumOccupationBasis (K:=ℝ) (p+c-s) (highestOccupation (h+1) (p+c-s)))))=
      (globalTypeILeftVector q hq hq1 h p s c r hs).val := by
  have he:=congrArg (TensorProduct.assoc ℝ (quantumOccupationSpace ℝ (Fin (h+2)) (p+r))
    (quantumOccupationSpace ℝ (Fin (h+2)) (s+r)) (quantumOccupationSpace ℝ (Fin (h+2)) c))
      (globalMixedSymVertex_highest_factor q hq hq1 h p s c hs r)
  change _=(TensorProduct.assoc ℝ (quantumOccupationSpace ℝ (Fin (h+2)) (p+r))
    (quantumOccupationSpace ℝ (Fin (h+2)) (s+r)) (quantumOccupationSpace ℝ (Fin (h+2)) c))
    ((TensorProduct.assoc ℝ (quantumOccupationSpace ℝ (Fin (h+2)) (p+r))
      (quantumOccupationSpace ℝ (Fin (h+2)) (s+r)) (quantumOccupationSpace ℝ (Fin (h+2)) c)).symm
      (globalTypeILeftVector q hq hq1 h p s c r hs).val) at he
  rw [LinearEquiv.apply_symm_apply] at he
  exact he

theorem amsSharedNative_TypeI_right_highest (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a p s d : ℕ) (hbal : a+p=s+d) (hs : s≤a) (r : ℕ) :
    TensorProduct.map LinearMap.id (globalReverseMixedPairClebsch q hq hq1 (h+1) (by omega) p s r)
      (((-1:ℝ)^(h*s) • globalSymMixedVertex q hq hq1 h a p s d hbal hs)
        (quantumOccupationBasis (K:=ℝ) d (highestOccupation (h+1) d)))=
      (globalTypeIRightVector q hq hq1 h a p s r hs).val := by
  rw [LinearMap.smul_apply,map_smul]
  change (-1:ℝ)^(h*s) • (globalSharedTypeIRightTree q hq hq1 h a p s d hbal hs r
    (quantumOccupationBasis (K:=ℝ) d (highestOccupation (h+1) d)))=_
  rw [globalSharedTypeIRightTree_highest,smul_smul,← mul_pow]
  norm_num

theorem amsSharedNative_TypeII_left_highest (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d) :
    nativeTypeIITwoRowInclusion q hq hq1 (h+1) (by omega) a b c d r
      (((-1:ℝ)^(h*c) • nativeTypeIIOuterVertex q hq hq1 (h+1) (by omega) a b c d hbal r)
        (quantumOccupationBasis (K:=ℝ) d (highestOccupation (h+1) d)))=
      (-1:ℝ)^(h*c) • (physicalTypeIICalibratedLeft q hq hq1 h a b c d hbal r).val := by
  rw [LinearMap.smul_apply,map_smul]
  exact congrArg (fun v=>(-1:ℝ)^(h*c) • v)
    (nativeTypeIIOuterVertex_calibrated_highest q hq hq1 h a b c d hbal r)

theorem amsSharedNative_TypeII_right_highest (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a p s d : ℕ) (hbal : a+p=s+d) (hs : s≤a) (r : ℕ) :
    TensorProduct.map LinearMap.id (globalAMSMixedIn q hq hq1 h p s r)
      (((-1:ℝ)^(h*s) • globalSymMixedVertex q hq hq1 h a p s d hbal hs)
        (quantumOccupationBasis (K:=ℝ) d (highestOccupation (h+1) d)))=
      (-1:ℝ)^(h*(s+r)) • (globalTypeIIRightVector q hq hq1 h a p s d hbal hs r).val := by
  unfold globalAMSMixedIn
  rw [TensorProduct.map_smul_right,LinearMap.smul_apply,LinearMap.smul_apply,map_smul,smul_smul,
    globalTypeIIRightVertex_highest_factor]
  congr 1
  simp only [Nat.mul_add,pow_add]
  ring

theorem amsSharedNative_common_phase_cancels {V : Type*} [AddCommGroup V] [Module ℝ V]
    (h c : ℕ) (B : LinearMap.BilinForm ℝ V) (v w : V) :
    B ((-1:ℝ)^(h*c) • v) ((-1:ℝ)^(h*c) • w)=B v w := by
  simp only [map_smul,LinearMap.smul_apply,smul_eq_mul]
  have he : (-1:ℝ)^(h*c)*(-1:ℝ)^(h*c)=1 := by rw [← mul_pow];norm_num
  calc
    _ = ((-1:ℝ)^(h*c)*(-1:ℝ)^(h*c))*B v w := by ring
    _ = _ := by rw [he,one_mul]

end AMSPhysical
#print axioms AMSPhysical.amsSharedNative_TypeI_left_highest
#print axioms AMSPhysical.amsSharedNative_TypeI_right_highest
#print axioms AMSPhysical.amsSharedNative_TypeII_left_highest
#print axioms AMSPhysical.amsSharedNative_TypeII_right_highest
#print axioms AMSPhysical.amsSharedNative_common_phase_cancels
