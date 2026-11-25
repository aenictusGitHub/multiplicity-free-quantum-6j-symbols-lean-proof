import TypeIIReferenceWigner

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

/-- Precise reduction of the remaining Type-II AMS entry obligation to the
higher-rank ACTUAL overlap equality. This is an equivalence of obligations,
not a proof that either side holds. The same arbitrary phase factor appears
on both sides, and the physical dimensions are independently proved positive. -/
theorem physicalTypeII_AMS_entry_iff_overlap (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d) (t : QuantumCupIndex a c b) (eps : ℝ) :
    physicalTypeIIWignerSymbol q hq hq1 h a b c d hbal r t=
      eps*(amsFourTrianglePrefactor q h (a:ℤ) b c d (typeIILeftLabel a b r.val) (typeIIRightLabel b c t.val.val)*
        AMSGeneral.kernel (quantumFactorialInt q) h true (a:ℤ) b c d
          (typeIILeftLabel a b r.val) (typeIIRightLabel b c t.val.val)) ↔
    physicalTypeIIRecouplingMatrix q hq hq1 (h+1) (by omega) a b c d hbal r t=
      eps*quantumRacahMatrix q hq hq1 (a+h) (b+h) c
        (typeIIShiftedLeftPath h a b c d hbal r) (typeIIShiftedRightPath h a b c t) := by
  rw [← typeIIShiftedReferenceWigner_AMS q hq hq1 h a b c d hbal r t]
  unfold physicalTypeIIWignerSymbol typeIIShiftedReferenceWigner
  have hD : Real.sqrt (twoRowIrrepQuantumDimension q hq hq1 (h+1) (by omega) ((a-r.val)+(b-r.val)) r.val*
      mixedIrrepQuantumDimension q hq hq1 (h+1) (by omega) (b-(c-t.val.val)) t.val.val)≠0 :=
    ne_of_gt (Real.sqrt_pos.mpr (mul_pos
      (twoRowIrrepQuantumDimension_pos q hq hq1 (h+1) (by omega) _ _)
      (mixedIrrepQuantumDimension_pos q hq hq1 (h+1) (by omega) _ _)))
  constructor
  · intro he
    have ht:=congrArg (fun x : ℝ =>x*Real.sqrt
      (twoRowIrrepQuantumDimension q hq hq1 (h+1) (by omega) ((a-r.val)+(b-r.val)) r.val*
        mixedIrrepQuantumDimension q hq hq1 (h+1) (by omega) (b-(c-t.val.val)) t.val.val)) he
    field_simp [hD] at ht
    exact ht
  · intro he
    rw [he]
    ring

/-- Exact global row/column gauge equivalence of the two remaining Type-II
obligations. This preserves separately chosen channel signs and does not
replace them by independent entry signs. Neither obligation is assumed. -/
theorem physicalTypeII_AMS_gauge_iff_overlap (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a b c d : ℕ) (hbal : a+b=c+d) :
    (∃ eps : TypeIICommonIndex a b c d → ℝ,∃ eta : QuantumCupIndex a c b → ℝ,
      (∀ r,eps r=1 ∨ eps r= -1) ∧ (∀ t,eta t=1 ∨ eta t= -1) ∧
      ∀ r t,physicalTypeIIWignerSymbol q hq hq1 h a b c d hbal r t=
        (eps r*eta t)*(amsFourTrianglePrefactor q h (a:ℤ) b c d
          (typeIILeftLabel a b r.val) (typeIIRightLabel b c t.val.val)*
          AMSGeneral.kernel (quantumFactorialInt q) h true (a:ℤ) b c d
            (typeIILeftLabel a b r.val) (typeIIRightLabel b c t.val.val))) ↔
    (∃ eps : TypeIICommonIndex a b c d → ℝ,∃ eta : QuantumCupIndex a c b → ℝ,
      (∀ r,eps r=1 ∨ eps r= -1) ∧ (∀ t,eta t=1 ∨ eta t= -1) ∧
      ∀ r t,physicalTypeIIRecouplingMatrix q hq hq1 (h+1) (by omega) a b c d hbal r t=
        (eps r*eta t)*quantumRacahMatrix q hq hq1 (a+h) (b+h) c
          (typeIIShiftedLeftPath h a b c d hbal r) (typeIIShiftedRightPath h a b c t)) := by
  constructor
  · rintro ⟨eps,eta,heps,heta,hEq⟩
    refine ⟨eps,eta,heps,heta,?_⟩
    intro r t
    exact (physicalTypeII_AMS_entry_iff_overlap q hq hq1 h a b c d hbal r t (eps r*eta t)).mp (hEq r t)
  · rintro ⟨eps,eta,heps,heta,hEq⟩
    refine ⟨eps,eta,heps,heta,?_⟩
    intro r t
    exact (physicalTypeII_AMS_entry_iff_overlap q hq hq1 h a b c d hbal r t (eps r*eta t)).mpr (hEq r t)

end AMSPhysical
#print axioms AMSPhysical.physicalTypeII_AMS_entry_iff_overlap

#print axioms AMSPhysical.physicalTypeII_AMS_gauge_iff_overlap
