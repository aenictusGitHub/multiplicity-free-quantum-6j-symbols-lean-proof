import TypeIIShiftedTriangles

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

theorem typeIIShifted_kernel (F : ℤ → ℝ) (h a b c d : ℕ) (hbal : a+b=c+d)
    (r : TypeIICommonIndex a b c d) (t : QuantumCupIndex a c b) :
    AMSGeneral.kernel F 0 false ((a+h:ℕ):ℤ) ((b+h:ℕ):ℤ) c d
      (coupledLabel (a+h) (b+h) (typeIIShiftedLeftPath h a b c d hbal r).1)
      (coupledLabel (b+h) c (typeIIShiftedRightPath h a b c t).1)=
    (-1:ℝ)^h*AMSGeneral.kernel F h true (a:ℤ) b c d
      (typeIILeftLabel a b r.val) (typeIIRightLabel b c t.val.val) := by
  rw [typeIIShiftedLeft_label,typeIIShiftedRight_label]
  have he:=AMSGeneral.shifted_kernel_typeII F h (a:ℤ) b c d
    (typeIILeftLabel a b r.val) (typeIIRightLabel b c t.val.val)
  simpa only [Nat.cast_add] using he

/-- Independently constructed physical STANDARD rank-two overlap at precisely
the AMS Type-II shifted labels, evaluated as the source factorial kernel. -/
theorem typeIIShifted_physicalRacah_kernel (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d) (t : QuantumCupIndex a c b) :
    quantumRacahMatrix q hq hq1 (a+h) (b+h) c
      (typeIIShiftedLeftPath h a b c d hbal r) (typeIIShiftedRightPath h a b c t)=
      (-1:ℝ)^(a+b)*Real.sqrt (qnum q (typeIILeftLabel a b r.val+1)*qnum q (typeIIRightLabel b c t.val.val+h+1))*
        Real.sqrt (typeIILeftShiftedTriangleSq q h a b c d r.val*typeIIRightShiftedTriangleSq q h a b c t.val.val)*
          AMSGeneral.kernel (quantumFactorialInt q) h true (a:ℤ) b c d
            (typeIILeftLabel a b r.val) (typeIIRightLabel b c t.val.val) := by
  have he:=physical_rank_two_AMS_standard q hq hq1 (a+h) (b+h) c d
    (typeIIShiftedFixedLeftPath h a b c d hbal r) (typeIIShiftedRightPath h a b c t)
    (typeIIShiftedRight_total h a b c d hbal t)
  rw [typeIIShifted_defect h a b c d hbal r] at he
  dsimp only [typeIIShiftedFixedLeftPath] at he
  have hp : a+h+(b+h)+c-(c+h)=a+b+h := by omega
  rw [hp,standardRacahPrefactor_dimensions q hq,typeIIShifted_wignerTrianglePrefactor] at he
  rw [typeIIShifted_kernel,typeIIShiftedLeft_label,typeIIShiftedRight_label,pow_add] at he
  have hs:=AMSGeneral.sign_square (𝕂:=ℝ) h
  calc
    _ = _ := he
    _ = _ := by
      calc
        _ = ((-1:ℝ)^h*(-1:ℝ)^h)*((-1:ℝ)^(a+b)*
          Real.sqrt (qnum q (typeIILeftLabel a b r.val+1)*qnum q (typeIIRightLabel b c t.val.val+h+1))*
          Real.sqrt (typeIILeftShiftedTriangleSq q h a b c d r.val*typeIIRightShiftedTriangleSq q h a b c t.val.val)*
          AMSGeneral.kernel (quantumFactorialInt q) h true (a:ℤ) b c d
            (typeIILeftLabel a b r.val) (typeIIRightLabel b c t.val.val)) := by ring
        _ = _ := by rw [hs,one_mul]

end AMSPhysical
#print axioms AMSPhysical.typeIIShifted_physicalRacah_kernel
