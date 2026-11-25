import QNumberPowerBridge
import QuantumDiagonalPhases
import QuantumRacahRates

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000
noncomputable section
namespace AMSPhysical

/-- Instantiate the rational diagonal certificate at the actual quantum powers. -/
theorem sl2ProjectedDiagonal_rates_regular (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (i m n r s : ℤ) (hi : 0< i) :
    sl2ProjectedDiagonal q i m n r s=q^(m+n+1)+q^(-(m+n+1))-
      sl2RacahBirth q (i-m+2*r) m n r s-sl2RacahDeath q (i-m+2*r) m n r s := by
  have hq0 := ne_of_gt hq
  have hD : q^2-1≠0 := by
    simpa only [zpow_one] using qpow_square_sub_one_ne q hq hq1 1 (by norm_num)
  have h0 := qpow_square_sub_one_ne q hq hq1 i (by omega)
  have h1 := qpow_square_sub_one_ne q hq hq1 (i+1) (by omega)
  rw [zpow_add₀ hq0,zpow_one,mul_pow] at h1
  have h2 := qpow_square_sub_one_ne q hq hq1 (i+2) (by omega)
  simp only [zpow_add₀ hq0,zpow_ofNat,mul_pow,← pow_mul] at h2
  have hc := casimir_diagonal_rational q (q^i) (q^m) (q^n) (q^r) (q^s)
    hq0 (zpow_ne_zero _ hq0) (zpow_ne_zero _ hq0) (zpow_ne_zero _ hq0)
    (zpow_ne_zero _ hq0) (zpow_ne_zero _ hq0) hD h0 h1 h2
  simp only [symmetricQNumber_two_mul_q_div q hq0,symmetricQNumber_two_mul_q q hq0,
    symmetricQNumber_mul_q_div q hq0,symmetricQNumber_mul_q_sq q hq0,
    symmetricQNumber_mul_q q hq0,symmetricQNumber_div q hq0,symmetricQNumber_zpow] at hc
  have hD1 : (q-q⁻¹)^2/q^i=(q-q⁻¹)^2*q^(-i) := by
    simp only [div_eq_mul_inv,zpow_neg]
  have hD2 : (q-q⁻¹)^2/(q^i*q^2)=(q-q⁻¹)^2*q^(-i-2) := by
    simp only [zpow_sub₀ hq0,zpow_neg,zpow_ofNat,div_eq_mul_inv,mul_inv_rev]
    ring
  rw [mul_div_assoc (qInteger q (m-r+1)*qInteger q r) (q^n) ((q^s)^2),
    qpow_div_square q hq0 n s,qpow_square_div q hq0 r m,
    qpow_weight_pair q hq0 m n r s,qpow_weight_pair_inv q hq0 m n r s,hD1,hD2,
    qpow_scalar_casimir q hq0 m n,← zpow_neg q (m+n+1)] at hc
  have hp : i+r-m+1=i-m+r+1 := by ring
  rw [hp] at hc
  unfold sl2ProjectedDiagonal sl2DiagonalWeight sl2RacahBirth sl2RacahDeath
  have hL1 : (i-m+2*r)+m-2*r=i := by ring
  have hL2 : (i-m+2*r)+m-r+1=i+r+1 := by ring
  have hL3 : (i-m+2*r)-r+1=i-m+r+1 := by ring
  rw [hL1,hL2,hL3]
  simp only [div_eq_mul_inv,mul_inv_rev] at hc ⊢
  linear_combination hc

end AMSPhysical

#print axioms AMSPhysical.sl2ProjectedDiagonal_rates_regular
