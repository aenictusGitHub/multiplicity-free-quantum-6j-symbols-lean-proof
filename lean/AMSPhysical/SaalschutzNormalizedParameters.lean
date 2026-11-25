import SaalschutzParameters

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
noncomputable section
namespace AMSPhysical

theorem saalschutz_QN_ne (Q : ℝ) (hQ : 0<Q) (hQ1 : Q≠1) (n : ℕ) : Q*Q^n-1≠0 := by
  have h := baseQ_factor_nonzero Q hQ hQ1 n
  intro he
  apply h
  linarith

theorem SaalschutzGeneric.CN_ne {Q A B C : ℝ} (h : SaalschutzGeneric Q A B C)
    (hQ : Q≠0) (n : ℕ) : C*Q^n-1≠0 := by
  intro he
  exact h.C_power_ne_one hQ n (by rw [zpow_natCast];linarith)

theorem SaalschutzGeneric.CN_ABx_ne {Q A B C : ℝ} (h : SaalschutzGeneric Q A B C)
    (hQ : Q≠0) (n k : ℕ) : C*Q^n-A*B*Q^k≠0 := by
  intro he
  apply h.notScaledPower ((k:ℤ)-(n:ℤ))
  apply power_ratio_unique Q hQ C (A*B) n k
  simp only [zpow_natCast]
  exact sub_eq_zero.mp he

theorem SaalschutzGeneric.AB_CN_ne {Q A B C : ℝ} (h : SaalschutzGeneric Q A B C)
    (hQ : Q≠0) (n : ℕ) : A*B-C*Q^n≠0 := by
  have hn := h.CN_ABx_ne hQ n 0
  simp only [pow_zero,mul_one] at hn
  exact sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp hn))

theorem normalizedD_eq (Q A B C : ℝ) (n : ℕ) :
    A*B/(C*Q^n)=A*B*Q^(-(n:ℤ))/C := by
  simp only [div_eq_mul_inv,mul_inv_rev,zpow_neg,zpow_natCast]
  ring

theorem SaalschutzGeneric.D_factor {Q A B C : ℝ} (h : SaalschutzGeneric Q A B C)
    (hQ : Q≠0) (n k : ℕ) : 1-(A*B/(C*Q^n))*Q^k≠0 := by
  rw [normalizedD_eq]
  exact h.scaled_factor hQ _ k

theorem saalschutz_U_ne (Q : ℝ) (hQ : 0<Q) (hQ1 : Q≠1) (n : ℕ) :
    1-(Q*Q^n)⁻¹≠0 := by
  intro he
  have hh := saalschutz_QN_ne Q hQ hQ1 n
  apply hh
  have hn : Q*Q^n≠0 := mul_ne_zero (ne_of_gt hQ) (pow_ne_zero _ (ne_of_gt hQ))
  field_simp [hn] at he
  linarith

end AMSPhysical

#print axioms AMSPhysical.SaalschutzGeneric.CN_ABx_ne
