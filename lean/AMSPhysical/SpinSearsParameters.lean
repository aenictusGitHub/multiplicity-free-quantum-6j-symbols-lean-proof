import SpinRacahParameters
import SpinRacahScale
import BasicFourTerm

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

theorem spinRacah_top_degree_power (Q : ℝ) (hQ : Q≠0) (m n u : ℕ) :
    spinRacahA Q m*spinRacahA Q n*Q*Q^u=Q^((u:ℤ)-(m:ℤ)-(n:ℤ)-1) := by
  unfold spinRacahA
  have hq : Q=Q^(1:ℤ) := (zpow_one Q).symm
  conv_lhs => arg 1;arg 2;rw [hq]
  rw [← zpow_natCast Q u,← zpow_add₀ hQ,← zpow_add₀ hQ,← zpow_add₀ hQ]
  congr 1
  ring

theorem spinRacah_top_grid_power (Q : ℝ) (hQ : Q≠0) (l m R : ℕ) (r : ℤ) :
    spinRacahA Q R*spinRacahFourth Q l m R*Q*Q^r=Q^(r-(l:ℤ)-(m:ℤ)-1) := by
  unfold spinRacahA spinRacahFourth
  have hq : Q=Q^(1:ℤ) := (zpow_one Q).symm
  conv_lhs => arg 1;arg 2;rw [hq]
  rw [← zpow_add₀ hQ,← zpow_add₀ hQ,← zpow_add₀ hQ]
  congr 1
  ring

theorem spinRacahFunction_basic4 (Q : ℝ) (hQ : Q≠0) (l m n R u r : ℕ) :
    spinRacahFunction Q l m n R u r=
      ∑ k∈Finset.range (u+1),basic4Term Q (Q^(-(r:ℤ)))
        (Q^((u:ℤ)-(m:ℤ)-(n:ℤ)-1)) (Q^((r:ℤ)-(l:ℤ)-(m:ℤ)-1)) (Q^(-(u:ℤ)))
        (Q^((R:ℤ)-(l:ℤ)-(m:ℤ)-(n:ℤ)-1)) (Q^(-(m:ℤ))) (Q^(-(R:ℤ))) k := by
  unfold spinRacahFunction qRacahSeries
  apply Finset.sum_congr rfl
  intro k hk
  rw [qRacahTerm_basic4,spinRacah_top_degree_power Q hQ,spinRacah_top_grid_power Q hQ,
    spinRacahA_mul Q hQ,spinRacahBD_mul Q hQ,spinRacahA_mul Q hQ]
  have hr : (Q^(r:ℤ))⁻¹=Q^(-(r:ℤ)) := (zpow_neg Q r).symm
  have hu : (Q^u)⁻¹=Q^(-(u:ℤ)) := by rw [zpow_neg,zpow_natCast]
  rw [hr,hu]
  unfold basic4Term
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

end AMSPhysical

#print axioms AMSPhysical.spinRacahFunction_basic4
