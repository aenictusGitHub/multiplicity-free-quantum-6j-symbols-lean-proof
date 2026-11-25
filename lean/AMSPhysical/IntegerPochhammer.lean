import QRacahUpperEndpoints

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

theorem qPochhammer_integer_power_nonzero (Q : ℝ) (hQ : 0<Q) (hQ1 : Q≠1) (a : ℤ) (n : ℕ)
    (ha : 0<a ∨ a≤-(n:ℤ)) : qPochhammer Q (Q^a) n≠0 := by
  apply qPochhammer_ne_zero
  intro k hk he
  rw [← zpow_natCast Q k,← zpow_add₀ (ne_of_gt hQ)] at he
  have hp : Q^(a+(k:ℤ))=Q^(0:ℤ) := by
    simpa only [zpow_zero] using (sub_eq_zero.mp he).symm
  have hz := zpow_right_injective₀ hQ hQ1 hp
  rcases ha with ha | ha <;> omega

theorem qPochhammer_integer_power_zero (Q : ℝ) (hQ : Q≠0) (a : ℤ) (n : ℕ)
    (ha : a≤0) (han : -(n:ℤ)<a) : qPochhammer Q (Q^a) n=0 := by
  let k := (-a).toNat
  have hcast : (k:ℤ)= -a := by dsimp [k];omega
  have hk : k<n := by omega
  have he : a=-(k:ℤ) := by omega
  rw [he]
  exact qPochhammer_terminates Q hQ k n hk

theorem qPochhammer_factor_of_nonzero (Q a : ℝ) (n : ℕ) (hp : qPochhammer Q a n≠0)
    (k : ℕ) (hk : k<n) : 1-a*Q^k≠0 :=
  (Finset.prod_ne_zero_iff.mp hp) k (Finset.mem_range.mpr hk)

theorem qRacahSeriesRegular_of_pochhammer (Q A B C D : ℝ) (n : ℕ)
    (hQ : qPochhammer Q Q n≠0) (hA : qPochhammer Q (A*Q) n≠0)
    (hB : qPochhammer Q (B*D*Q) n≠0) (hC : qPochhammer Q (C*Q) n≠0) :
    QRacahSeriesRegular Q A B C D n := by
  intro k hk
  exact ⟨qPochhammer_factor_of_nonzero Q Q n hQ k hk,
    qPochhammer_factor_of_nonzero Q (A*Q) n hA k hk,
    qPochhammer_factor_of_nonzero Q (B*D*Q) n hB k hk,
    qPochhammer_factor_of_nonzero Q (C*Q) n hC k hk⟩

end AMSPhysical

#print axioms AMSPhysical.qPochhammer_integer_power_nonzero
#print axioms AMSPhysical.qPochhammer_integer_power_zero
