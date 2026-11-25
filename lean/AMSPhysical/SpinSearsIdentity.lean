import SpinSearsParameters
import SearsAdmissible

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

/-- The all-admissible Sears conversion of the actual spin q-Racah parameters,
with no transformed-denominator restrictions. -/
theorem spinRacah_sears_cleared (Q : ℝ) (hQ : 0<Q) (hQ1 : Q≠1) (l m n R u r : ℕ)
    (h : SpinRacahAdmissible l m n R u) :
    spinRacahFunction Q l m n R u r*qPochhammer Q (Q^(-(m:ℤ))) u*qPochhammer Q (Q^(-(R:ℤ))) u=
      ∑ k∈Finset.range (u+1),searsClearedTerm Q (Q^(-(r:ℤ)))
        (Q^((u:ℤ)-(m:ℤ)-(n:ℤ)-1)) (Q^((r:ℤ)-(l:ℤ)-(m:ℤ)-1))
        (Q^((R:ℤ)-(l:ℤ)-(m:ℤ)-(n:ℤ)-1)) (Q^(-(m:ℤ))) (Q^(-(R:ℤ)))
        (Q^((u:ℤ)+(r:ℤ)-(m:ℤ)-(R:ℤ)-1)) u k := by
  have hq0 := ne_of_gt hQ
  rw [spinRacahFunction_basic4 Q hq0]
  apply qSears_cleared Q _ _ _ _ _ _ _ hQ hQ1
    (zpow_ne_zero _ hq0) (zpow_ne_zero _ hq0) (zpow_ne_zero _ hq0)
    (zpow_ne_zero _ hq0) (zpow_ne_zero _ hq0)
  · rw [← zpow_add₀ hq0,← zpow_add₀ hq0]
    congr 1
    ring
  · rw [← zpow_add₀ hq0,← zpow_add₀ hq0,← zpow_add₀ hq0]
    congr 1
    ring
  · have hh := h.rootSecond
    exact qPochhammer_integer_power_nonzero Q hQ hQ1 _ u (Or.inr (by omega))
  · have hh := h.middle
    exact qPochhammer_integer_power_nonzero Q hQ hQ1 _ u (Or.inr (by omega))
  · have hh := h.defect
    exact qPochhammer_integer_power_nonzero Q hQ hQ1 _ u (Or.inr (by omega))

end AMSPhysical

#print axioms AMSPhysical.spinRacah_sears_cleared
