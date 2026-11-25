import GlobalMixedCommutorBoundary
import GlobalTypeIRightFixedChannel
import GlobalTypeIIRightVertices

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical

/-- The Type-I and Type-II contraction-zero right outer vertices differ
by exactly one incident-triple sign. No exterior realization enters it. -/
theorem globalTypeIRightII_zero_comparison (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a p s d : ℕ) (hbal : a+p=s+d) (hs : s≤a) :
    physicalTypeIIToI q hq hq1 (h+1) (by omega) a p s
      (globalTypeIIRightVector q hq hq1 h a p s d hbal hs 0).val =
      (-1:ℝ)^(h*s) • (globalTypeIRightVector q hq hq1 h a p s 0 hs).val := by
  let E:=physicalTypeIIToCompleteI q hq hq1 (h+1) (by omega) a p s d hbal
  let v:=globalTypeIIRightVector q hq hq1 h a p s d hbal hs 0
  have hv : E v∈physicalTypeIRightChannelSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      (h+1) a s 0 p (globalTypeIIRightCupIndex a p s 0 hs) := by
    apply (physicalTypeIIToCompleteI_right_mem_iff q hq hq1 (h+1) (by omega) a p s d hbal
      (globalTypeIIRightCupIndex a p s 0 hs) v).mpr
    exact physicalTypeIICalibratedRight_mem q hq hq1 h a p s d hbal _
  have hN : physicalTripleBilin q (h+1) a s p (E v).val (E v).val=1 := by
    rw [physicalTypeIIToCompleteI_isometry]
    exact physicalTypeIICalibratedRight_unit q hq hq1 h a p s d hbal _
  obtain ⟨e,he,hV⟩:=physicalTypeIRightCoupling_unique_sign q hq hq1 (h+1) (by omega) a s 0 p
    (by omega) (Or.inl rfl) (globalTypeIIRightCupIndex a p s 0 hs) (E v) hv hN
  have hpos : 0 < physicalAllFirstFunctional (h+1) a s p (E v).val := by
    change 0 < physicalAllFirstFunctional (h+1) a s p
      (physicalTypeIIToCompleteI q hq hq1 (h+1) (by omega) a p s d hbal v).val
    rw [physicalTypeIIToCompleteI_val,physicalTypeIIToI_zero_boundary q hq hq1 (h+1) (by omega) a p s v.val
      (globalTypeIIRightVector_mem q hq hq1 h a p s d hbal hs 0)]
    exact mul_pos (zpow_pos hq _) (globalTypeIIRightVector_first_boundary_pos q hq hq1 h a p s d hbal hs 0)
  have hi:=physicalTypeIRightCoupling_first_boundary_signed_pos q hq hq1 (h+1) (by omega) a s 0 p
    (by omega) (Or.inl rfl) (globalTypeIIRightCupIndex a p s 0 hs)
  have hsign : typeIFirstBoundarySign (h+1) s
      (globalTypeIIRightCupIndex a p s 0 hs).val.val=(-1:ℝ)^(h*s) := by
    simp only [typeIFirstBoundarySign,quantumCupRankGauge,globalTypeIIRightCupIndex,
      Nat.add_sub_cancel,Nat.sub_self,pow_zero,mul_one]
  rw [hsign,physicalTypeIFirstBoundary_eq_allFirst] at hi
  rw [hV] at hpos
  simp only [Submodule.coe_smul_of_tower,map_smul,smul_eq_mul] at hpos
  let b:=physicalAllFirstFunctional (h+1) a s p (globalTypeIRightVector q hq hq1 h a p s 0 hs).val
  change 0 < (-1:ℝ)^(h*s)*b at hi
  change 0 < e*b at hpos
  have hsq : ((-1:ℝ)^(h*s))^2=1 := by rw [pow_two,← mul_pow];norm_num
  have hpm : (-1:ℝ)^(h*s)=1 ∨ (-1:ℝ)^(h*s)= -1 := (sq_eq_one_iff).mp hsq
  have heq : e=(-1:ℝ)^(h*s) := by
    rcases he with he|he <;> rcases hpm with hp|hp <;> first
      | exact he.trans hp.symm
      | rw [he] at hpos;rw [hp] at hi;nlinarith
  have heval:=congrArg Subtype.val hV
  change physicalTypeIIToI q hq hq1 (h+1) (by omega) a p s v.val =
    e • (globalTypeIRightVector q hq hq1 h a p s 0 hs).val at heval
  rw [heq] at heval
  exact heval

end AMSPhysical
#print axioms AMSPhysical.globalTypeIRightII_zero_comparison
