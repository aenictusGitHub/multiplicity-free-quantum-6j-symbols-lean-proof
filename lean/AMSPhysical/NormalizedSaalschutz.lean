import SaalschutzAdmissible

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

/-- The proved Saalschutz sum in normalized parameters, ready for cancellations in 4phi3. -/
theorem qPfaffSaalschutz_normalized (Q A B C : ℝ) (hQ : 0<Q) (hQ1 : Q≠1)
    (hA : A≠0) (hB : B≠0) (hC : C≠0) (n : ℕ)
    (hCP : qPochhammer Q C n≠0) (hDP : qPochhammer Q (A*B*Q/(C*Q^n)) n≠0)
    (hABP : qPochhammer Q (C/(A*B)) n≠0) :
    (∑ k∈Finset.range (n+1),basic3Term Q A B (Q^n)⁻¹ C (A*B*Q/(C*Q^n)) k)=
      qPochhammer Q (C/A) n*qPochhammer Q (C/B) n/
        (qPochhammer Q C n*qPochhammer Q (C/(A*B)) n) := by
  have hD : A*B*Q^(1-(n:ℤ))/C=A*B*Q/(C*Q^n) := by
    rw [zpow_sub₀ (ne_of_gt hQ),zpow_one,zpow_natCast]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  have h := qPfaffSaalschutz Q A B C hQ hQ1 hA hB hC n hCP (by rw [hD];exact hDP) hABP
  unfold saalschutzSum saalschutzProduct at h
  simp only [saalschutzTerm_normalized Q A B C (ne_of_gt hQ)] at h
  exact h

end AMSPhysical

#print axioms AMSPhysical.qPfaffSaalschutz_normalized
