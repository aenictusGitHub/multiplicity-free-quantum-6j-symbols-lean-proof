import SpinSearsNatural

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3000000
noncomputable section
namespace AMSPhysical

def spinRacahFactorialConstant (q : ℝ) (l m n R u r s : ℕ) : ℝ :=
  searsFactorialConstant q u r (l+u-R) (n-s) (m-r) s (l+m+n-R+1)*
    qfactorial q (m-u)*qfactorial q (R-u)/(qfactorial q m*qfactorial q R)

def spinRacahFactorialSum (q : ℝ) (l m n R u r s : ℕ) : ℝ :=
  ∑ k∈Finset.range (u+1),factorialRacahTerm q u r (l+u-R) (n-s) (m-r) s (l+m+n-R+1) k

theorem spinRacah_left_common_phase (q : ℝ) (hq : 0<q) (hq1 : q≠1) (m R u r s : ℕ)
    (hum : u≤m) (huR : u≤R) (hr : r≤m) (hR : r+s=R) :
    qPochhammer (q^2) (q^(-2*(m:ℤ))) u*qPochhammer (q^2) (q^(-2*(R:ℤ))) u=
      searsCommonPhase q u r (m-r) s*
        (qfactorial q m*qfactorial q R/(qfactorial q (m-u)*qfactorial q (R-u))) := by
  rw [qPochhammer_negative_phase_factorial q hq hq1 m u hum,
    qPochhammer_negative_phase_factorial q hq hq1 R u huR]
  have hphase : negativePochPhase q m u*negativePochPhase q R u=searsCommonPhase q u r (m-r) s := by
    unfold negativePochPhase searsCommonPhase
    have hD : (q-q⁻¹)^u*(q-q⁻¹)^u=(q-q⁻¹)^(2*u) := by rw [← pow_add];congr 1;omega
    have hq : q^(-(m:ℤ)*(u:ℤ)+(u.choose 2:ℤ))*q^(-(R:ℤ)*(u:ℤ)+(u.choose 2:ℤ))=
        q^(-(((m-r:ℕ):ℤ)+2*(r:ℤ)+(s:ℤ))*(u:ℤ)+2*(u.choose 2:ℤ)) := by
      rw [← zpow_add₀ (ne_of_gt hq)]
      congr 1
      have hrc : ((m-r:ℕ):ℤ)=(m:ℤ)-(r:ℤ) := by omega
      have hRc : (R:ℤ)=(r:ℤ)+(s:ℤ) := by omega
      rw [hrc,hRc]
      ring
    linear_combination (q-q⁻¹)^(2*u)*hq+
      q^(-(m:ℤ)*(u:ℤ)+(u.choose 2:ℤ))*q^(-(R:ℤ)*(u:ℤ)+(u.choose 2:ℤ))*hD
  calc
    _ = (negativePochPhase q m u*negativePochPhase q R u)*
      (qfactorial q m*qfactorial q R/(qfactorial q (m-u)*qfactorial q (R-u))) := by ring
    _ = _ := by rw [hphase]

/-- Exact conversion to the seven-denominator quantum Racah factorial sum,
including its nonzero lower summation bound and all physical endpoint labels. -/
theorem spinRacahFunction_factorial_sum (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (l m n R u r s : ℕ) (h : SpinRacahAdmissible l m n R u)
    (hr : r≤m) (hs : s≤n) (hR : r+s=R) :
    spinRacahFunction (q^2) l m n R u r=
      spinRacahFactorialConstant q l m n R u r s*spinRacahFactorialSum q l m n R u r s := by
  have hroot := h.rootFirst
  have hsum := h.rootSecond
  have hT : u≤l+m+n-R+1 := by omega
  have hrel : r+(l+u-R)+(n-s)+(m-r)+s+1=u+(l+m+n-R+1) := by omega
  have he := spinRacah_natural_sears q hq hq1 l m n R u r s h hr hs hR
  rw [naturalSearsSum_factorial q hq hq1 u r (l+u-R) (n-s) (m-r) s (l+m+n-R+1) hT hrel] at he
  have hLP := spinRacah_left_common_phase q hq hq1 m R u r s h.middle h.defect hr hR
  have he' : spinRacahFunction (q^2) l m n R u r*
      (qPochhammer (q^2) (q^(-2*(m:ℤ))) u*qPochhammer (q^2) (q^(-2*(R:ℤ))) u)=
    searsCommonPhase q u r (m-r) s*searsFactorialConstant q u r (l+u-R) (n-s) (m-r) s (l+m+n-R+1)*
      spinRacahFactorialSum q l m n R u r s := by simpa only [mul_assoc,spinRacahFactorialSum] using he
  rw [hLP] at he'
  have hc := searsCommonPhase_nonzero q hq hq1 u r (m-r) s
  have hl : qfactorial q m*qfactorial q R/(qfactorial q (m-u)*qfactorial q (R-u))≠0 :=
    div_ne_zero (mul_ne_zero (qfactorial_ne_zero q hq m) (qfactorial_ne_zero q hq R))
      (mul_ne_zero (qfactorial_ne_zero q hq (m-u)) (qfactorial_ne_zero q hq (R-u)))
  have hcancel : spinRacahFunction (q^2) l m n R u r*
      (qfactorial q m*qfactorial q R/(qfactorial q (m-u)*qfactorial q (R-u)))=
    searsFactorialConstant q u r (l+u-R) (n-s) (m-r) s (l+m+n-R+1)*
      spinRacahFactorialSum q l m n R u r s := by
    apply mul_left_cancel₀ hc
    linear_combination he'
  have hx := (eq_div_iff hl).mpr hcancel
  rw [hx]
  unfold spinRacahFactorialConstant
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
  ring

end AMSPhysical

#print axioms AMSPhysical.spinRacahFunction_factorial_sum
