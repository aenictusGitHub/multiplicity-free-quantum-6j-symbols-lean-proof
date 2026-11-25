import QuantumTypeIILeftNormClosed

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 700000
noncomputable section
namespace AMSPhysical

/-- The actual Type-II tree norm in a single positive factorial quotient.
The common rank factorial cancels from the physical trace ratio. -/
theorem physicalTypeIILeftHighestNormSq_factorial (q:ℝ) (hq:0<q) (hq1:q≠1)
    (n:ℕ) (hn:0<n) (a b c d:ℕ) (hbal:a+b=c+d) (r:TypeIICommonIndex a b c d) :
    let i:=(a-r.val)+(b-r.val)
    physicalTypeIILeftHighestNormSq q hq hq1 n hn a b c d hbal r=
      qnum q (i+1)*qfactorial q (i+r.val+n)*qfactorial q (r.val+n-1)*qfactorial q d/
        (qfactorial q (i+r.val+1)*qfactorial q r.val*qfactorial q (n-1)*qfactorial q (n+d)) := by
  dsimp only
  rw [physicalTypeIILeftHighestNormSq_closed,twoRowIrrepQuantumDimension_closed]
  unfold symmetricQuantumDimension
  have hf(k:ℕ):qfactorial q k≠0:=ne_of_gt (qfactorial_pos q hq k)
  field_simp [hf]

end AMSPhysical
#print axioms AMSPhysical.physicalTypeIILeftHighestNormSq_factorial
