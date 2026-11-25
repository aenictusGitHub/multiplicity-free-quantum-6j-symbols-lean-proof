import SpinRacahParameters

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

theorem spinRacah_B_over_C (Q : ℝ) (hQ : Q≠0) (n R : ℕ) :
    spinRacahA Q n/spinRacahA Q R=Q^((R:ℤ)-(n:ℤ)) := by
  unfold spinRacahA
  rw [← zpow_sub₀ hQ]
  congr 1
  ring

theorem spinRacah_ABQ_over_C (Q : ℝ) (hQ : Q≠0) (m n R : ℕ) :
    spinRacahA Q m*spinRacahA Q n*Q/spinRacahA Q R=Q^((R:ℤ)-(m:ℤ)-(n:ℤ)) := by
  unfold spinRacahA
  rw [← zpow_add₀ hQ,zpow_mul_base Q hQ,← zpow_sub₀ hQ]
  congr 1
  ring

theorem spinRacah_A_over_CD (Q : ℝ) (hQ : Q≠0) (l m R : ℕ) :
    spinRacahA Q m/(spinRacahA Q R*spinRacahFourth Q l m R)=Q^((l:ℤ)+1) := by
  unfold spinRacahA spinRacahFourth
  rw [← zpow_add₀ hQ,← zpow_sub₀ hQ]
  congr 1
  ring

theorem spinRacah_D_inv (Q : ℝ) (l m R : ℕ) :
    (spinRacahFourth Q l m R)⁻¹=Q^((l:ℤ)+(m:ℤ)-(R:ℤ)+1) := by
  unfold spinRacahFourth
  rw [← zpow_neg]
  congr 1
  ring

theorem spinRacah_D_over_AN (Q : ℝ) (hQ : Q≠0) (l m R u : ℕ) :
    spinRacahFourth Q l m R/(spinRacahA Q m*Q^u)=Q^((R:ℤ)-(l:ℤ)-(u:ℤ)) := by
  unfold spinRacahA spinRacahFourth
  rw [← zpow_natCast Q u,← zpow_add₀ hQ,← zpow_sub₀ hQ]
  congr 1
  ring

theorem spinRacah_AQ_over_D (Q : ℝ) (hQ : Q≠0) (l m R : ℕ) :
    spinRacahA Q m*Q/spinRacahFourth Q l m R=Q^((l:ℤ)-(R:ℤ)+1) := by
  rw [spinRacahA_mul Q hQ]
  unfold spinRacahFourth
  rw [← zpow_sub₀ hQ]
  congr 1
  ring

end AMSPhysical

#print axioms AMSPhysical.spinRacah_ABQ_over_C
