import PhysicalTypeIAMSFormula

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical

/-- Independent physical overlap normalization before evaluating any AMS sum. -/
theorem physicalTypeIWigner_overlap_normalization (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h l m c:ℕ) (hadm:m≤l+c) (s t:QuantumCupIndex l m c):
    physicalTypeIWignerSymbol q hq hq1 h l m c hadm s t=
      (-1:ℝ)^(l+c)*quantumRacahMatrix q hq hq1 l (m+h) c
        (quantumCupLeftPath l m h c s) (quantumCupRightPath l m h c t)/
      Real.sqrt (mixedWeyl (qfactorial q) (qnum q) h (l-s.val.val) (m-s.val.val)*
        mixedWeyl (qfactorial q) (qnum q) h (c-(m-t.val.val)) t.val.val) := by
  unfold physicalTypeIWignerSymbol
  have ho:=physicalTypeICoupling_overlap_rankTwo q hq hq1 (h+1) (by omega) l m 0 c hadm (Or.inl rfl) s t
  rw [show 0+(h+1)-1=h from by omega] at ho
  simp only [Nat.add_zero] at ho
  rw [ho,← mixedWeyl_actual_dimension q hq hq1 h (l-s.val.val) (m-s.val.val),
    ← mixedWeyl_actual_dimension q hq hq1 h (c-(m-t.val.val)) t.val.val]

end AMSPhysical
#print axioms AMSPhysical.physicalTypeIWigner_overlap_normalization
