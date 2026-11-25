import TypeIIBoundaryCreationRecurrence

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1200000
noncomputable section
namespace AMSPhysical

/-- Determinant-background rescaling intertwines the complete two-term
creation recurrence, with the zero endpoint included. -/
theorem quantumDeterminantDifference (q:ℝ) (hq:0<q) (h b c k:ℕ) (α:ℝ)
    (f g:ℕ → ℝ) (hk:g k=α*q^(-(h:ℤ)*(k:ℤ))*f k)
    (hp:k≠0 → g (k-1)=α*q^(-(h:ℤ)*((k-1:ℕ):ℤ))*f (k-1)):
    q^(-(b:ℤ)-(c:ℤ)+2*(k:ℤ))*g k-
      q^(-(h:ℤ)-1-(b:ℤ)-(c:ℤ))*(if k=0 then 0 else g (k-1))=
    α*q^(-(h:ℤ)*(k:ℤ))*
      (q^(-(b:ℤ)-(c:ℤ)+2*(k:ℤ))*f k-
        q^(-1-(b:ℤ)-(c:ℤ))*(if k=0 then 0 else f (k-1))) := by
  rw [hk]
  by_cases hz:k=0
  · rw [if_pos hz,if_pos hz,mul_zero,mul_zero,sub_zero,sub_zero]
    ring
  · rw [if_neg hz,if_neg hz,hp hz]
    have he:q^(-(h:ℤ)-1-(b:ℤ)-(c:ℤ))*q^(-(h:ℤ)*((k-1:ℕ):ℤ))=
        q^(-(h:ℤ)*(k:ℤ))*q^(-1-(b:ℤ)-(c:ℤ)):=by
      rw [← zpow_add₀ (ne_of_gt hq),← zpow_add₀ (ne_of_gt hq)]
      congr 1
      have hcast:((k-1:ℕ):ℤ)=(k:ℤ)-1:=by omega
      rw [hcast]
      ring
    linear_combination -α*f (k-1)*he

end AMSPhysical
#print axioms AMSPhysical.quantumDeterminantDifference
