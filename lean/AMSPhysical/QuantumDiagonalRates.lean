import QuantumDiagonalRatesRegular
import JacobiDiagonalZeroAlgebra

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000
noncomputable section
namespace AMSPhysical

theorem sl2ProjectedDiagonal_rates_zero (q : ℝ) (hq : 0<q) (hq1 : q≠1) (r n : ℤ) :
    sl2ProjectedDiagonal q 0 r n r 0=q^(r+n+1)+q^(-(r+n+1))-
      sl2RacahBirth q r r n r 0-sl2RacahDeath q r r n r 0 := by
  have hq0 := ne_of_gt hq
  have hD : q^2-1≠0 := by
    simpa only [zpow_one] using qpow_square_sub_one_ne q hq hq1 1 (by norm_num)
  have hP : q^2+1≠0 := by nlinarith [sq_nonneg q]
  have hc := casimir_diagonal_rational_zero q (q^r) (q^n) hq0
    (zpow_ne_zero _ hq0) (zpow_ne_zero _ hq0) hD hP
  have hSym2 : symmetricQNumber q (q^2)=qInteger q 2 := symmetricQNumber_zpow q 2
  simp only [symmetricQNumber_zpow,hSym2] at hc
  have hK : q*q^n/q^r=q^(n-r+1) := by
    simp only [zpow_add₀ hq0,zpow_sub₀ hq0,zpow_one,div_eq_mul_inv]
    ring
  have hKi : q^r/(q*q^n)=q^(-(n-r+1)) := by
    have h := congrArg Inv.inv hK
    simpa only [inv_div,zpow_neg] using h
  have hD2 : (q-q⁻¹)^2/q^2=(q-q⁻¹)^2*q^(-2:ℤ) := by
    simp only [zpow_neg,zpow_ofNat,div_eq_mul_inv]
  rw [hK,hKi,hD2,qpow_scalar_casimir q hq0 r n,← zpow_neg q (r+n+1)] at hc
  unfold sl2ProjectedDiagonal sl2DiagonalWeight sl2RacahBirth sl2RacahDeath
  have hi : r+r-2*r=0 := by ring
  have hp : r+n-2*r+1=n-r+1 := by ring
  simp only [sub_self,sub_zero,zero_mul,mul_zero,add_zero,zero_add,neg_zero,zero_sub,
    qInteger_zero,qInteger_one q (qInteger_denominator_ne_zero q hq hq1),one_mul,mul_one,
    zero_div,div_one,hi] 
  rw [hp]
  simp only [div_eq_mul_inv,mul_inv_rev] at hc ⊢
  linear_combination hc

/-- The actual physical Casimir diagonal is the q-Racah birth/death diagonal,
including the zero intermediate-spin endpoint. -/
theorem quantumRacahJacobi_diagonal_birth_death (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n H : ℕ)
    (p : FixedLeftHighest l m n H) :
    quantumRacahJacobi q hq hq1 l m n H p p=quantumCasimirEigen q ((m:ℤ)+(n:ℤ))-
      sl2RacahBirth q l m n p.val.1.val p.val.2.val-sl2RacahDeath q l m n p.val.1.val p.val.2.val := by
  rw [quantumRacahJacobi_diagonal q hq hq1 l m n H p,casimirJacobiDiagonalClosed_integer q hq hq1]
  unfold quantumCasimirEigen
  have hl := channel_left_bound l m p.val.1
  have hm := channel_right_bound l m p.val.1
  have hs := channel_left_bound (coupledLabel l m p.val.1) n p.val.2
  by_cases hi : coupledLabel l m p.val.1=0
  · have hli : l=p.val.1.val := by unfold coupledLabel at hi;omega
    have hmi : m=p.val.1.val := by unfold coupledLabel at hi;omega
    have hsi : p.val.2.val=0 := by omega
    have hlic : (l:ℤ)=(p.val.1.val:ℤ) := by omega
    have hmic : (m:ℤ)=(p.val.1.val:ℤ) := by omega
    have hsic : (p.val.2.val:ℤ)=0 := by omega
    have hic : (coupledLabel l m p.val.1:ℤ)=0 := by omega
    rw [hic,hlic,hmic,hsic]
    exact sl2ProjectedDiagonal_rates_zero q hq hq1 _ _
  · have hc := sl2ProjectedDiagonal_rates_regular q hq hq1 (coupledLabel l m p.val.1) m n p.val.1.val p.val.2.val (by omega)
    have hlabel : (coupledLabel l m p.val.1:ℤ)-(m:ℤ)+2*(p.val.1.val:ℤ)=(l:ℤ) := by
      rw [coupledLabel_cast l m p.val.1.val hl hm]
      ring
    rw [hlabel] at hc
    exact hc

end AMSPhysical

#print axioms AMSPhysical.quantumRacahJacobi_diagonal_birth_death
