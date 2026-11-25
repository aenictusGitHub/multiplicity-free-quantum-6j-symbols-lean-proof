import ComplexPhysicalWigner

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical

theorem complexNormalizedOverlap_analyticAt (R D:ℂ → ℂ) (p q:ℂ)
    (hR:AnalyticAt ℂ R q) (hD:AnalyticAt ℂ D q) (hS:D q∈Complex.slitPlane):
    AnalyticAt ℂ (fun z:ℂ=>p*R z/complexPositiveRoot (D z)) q:=by
  have hs:AnalyticAt ℂ (fun z:ℂ=>complexPositiveRoot (D z)) q:=
    (complexPositiveRoot_analyticAt _ hS).comp (f:=D) (x:=q) hD
  exact (analyticAt_const.mul hR).fun_div hs (complexPositiveRoot_ne_zero _)

/-- A concrete holomorphic continuation of the independently defined actual
physical Type-I coefficient exists near every positive real q. -/
theorem complexPhysicalTypeIWigner_analyticAt_positive (q:ℝ) (hq:0<q)
    (h l m c:ℕ) (s t:QuantumCupIndex l m c):
    AnalyticAt ℂ (fun z:ℂ=>complexPhysicalTypeIWigner z h l m c s t) (q:ℂ):=by
  have hq0: (q:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (ne_of_gt hq)
  have hF:=complexQfactorial_ofReal_ne_zero q hq
  apply complexNormalizedOverlap_analyticAt
    (fun z=>complexRacahOverlap z l (m+h) c (quantumCupLeftPath l m h c s) (quantumCupRightPath l m h c t))
    (fun z=>complexMixedWeyl z h (l-s.val.val) (m-s.val.val)*
      complexMixedWeyl z h (c-(m-t.val.val)) t.val.val) ((-1:ℂ)^(l+c)) (q:ℂ)
  · exact complexRacahOverlap_analyticAt_positive q hq _ _ _ _ _
  · exact (complexMixedWeyl_analyticAt q hq0 hF _ _ _).mul (complexMixedWeyl_analyticAt q hq0 hF _ _ _)
  · rw [complexMixedWeyl_ofReal,complexMixedWeyl_ofReal,← Complex.ofReal_mul,Complex.ofReal_mem_slitPlane]
    exact mul_pos (mixedWeyl_quantum_pos q hq h (l-s.val.val) (m-s.val.val))
      (mixedWeyl_quantum_pos q hq h (c-(m-t.val.val)) t.val.val)

theorem complexPhysicalTypeIIWigner_analyticAt_positive (q:ℝ) (hq:0<q)
    (h a b c d:ℕ) (hbal:a+b=c+d) (r:TypeIICommonIndex a b c d) (t:QuantumCupIndex a c b):
    AnalyticAt ℂ (fun z:ℂ=>complexPhysicalTypeIIWigner z h a b c d hbal r t) (q:ℂ):=by
  have hq0:(q:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (ne_of_gt hq)
  have hF:=complexQfactorial_ofReal_ne_zero q hq
  apply complexNormalizedOverlap_analyticAt
    (fun z=>complexRacahOverlap z (a+h) (b+h) c
      (typeIIShiftedLeftPath h a b c d hbal r) (typeIIShiftedRightPath h a b c t))
    (fun z=>complexSameWeyl z h (a-r.val) (b-r.val) r.val*
      complexMixedWeyl z h (b-(c-t.val.val)) t.val.val) ((-1:ℂ)^(a+b)) (q:ℂ)
  · exact complexRacahOverlap_analyticAt_positive q hq _ _ _ _ _
  · exact (complexSameWeyl_analyticAt q hq0 hF _ _ _ _).mul (complexMixedWeyl_analyticAt q hq0 hF _ _ _)
  · rw [complexSameWeyl_ofReal,complexMixedWeyl_ofReal,← Complex.ofReal_mul,Complex.ofReal_mem_slitPlane]
    exact mul_pos (sameWeyl_quantum_pos q hq h (a-r.val) (b-r.val) r.val)
      (mixedWeyl_quantum_pos q hq h (b-(c-t.val.val)) t.val.val)

end AMSPhysical
#print axioms AMSPhysical.complexPhysicalTypeIIWigner_analyticAt_positive
