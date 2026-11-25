import SpinRacahScale
import QuantumFactorials

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

def integerQuantumProduct (q : ℝ) (a : ℤ) (k : ℕ) : ℝ :=
  ∏ j ∈ Finset.range k,qInteger q (a+(j:ℤ))

theorem integerQuantumProduct_succ (q : ℝ) (a : ℤ) (k : ℕ) :
    integerQuantumProduct q a (k+1)=integerQuantumProduct q a k*qInteger q (a+(k:ℤ)) :=
  Finset.prod_range_succ _ _

/-- Conversion of any integral q-Pochhammer parameter to a product of
symmetric quantum integers, with its exact phase. -/
theorem qPochhammer_symmetric_product (q : ℝ) (hq : 0<q) (hq1 : q≠1) (a : ℤ) (k : ℕ) :
    qPochhammer (q^2) (q^(2*a)) k=
      (-(q-q⁻¹))^k*q^(a*(k:ℤ)+(k.choose 2:ℤ))*integerQuantumProduct q a k := by
  have hq0 := ne_of_gt hq
  induction k with
  | zero => simp [qPochhammer_zero,integerQuantumProduct]
  | succ k ih =>
    rw [qPochhammer_succ,ih,integerQuantumProduct_succ]
    have hpow : q^(2*a)*(q^2)^k=q^(2*(a+(k:ℤ))) := by
      rw [← zpow_natCast (q^2) k,square_zpow_even,← zpow_add₀ hq0]
      congr 1
      ring
    rw [hpow,one_sub_qpow_double q hq0 (qInteger_denominator_ne_zero q hq hq1)]
    have hphase : q^(a*(k:ℤ)+(k.choose 2:ℤ))*q^(a+(k:ℤ))=
        q^(a*((k+1:ℕ):ℤ)+((k+1).choose 2:ℤ)) := by
      rw [← zpow_add₀ hq0,Nat.choose_succ_succ]
      simp only [Nat.choose_one_right,Nat.cast_add,Nat.cast_one]
      congr 1
      ring
    rw [pow_succ]
    linear_combination (-(q-q⁻¹))^(k+1)*integerQuantumProduct q a k*qInteger q (a+(k:ℤ))*hphase

theorem integerQuantumProduct_negative_cleared (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (a k : ℕ) (hk : k≤a) :
    integerQuantumProduct q (-(a:ℤ)) k*qfactorial q (a-k)=(-1:ℝ)^k*qfactorial q a := by
  induction k with
  | zero => simp [integerQuantumProduct]
  | succ k ih =>
    have hka : k≤a := by omega
    have harg : -(a:ℤ)+(k:ℤ)=-((a-k:ℕ):ℤ) := by omega
    have hs : a-k=(a-(k+1))+1 := by omega
    rw [integerQuantumProduct_succ,harg,qInteger_neg,← qnum_eq_qInteger q hq hq1]
    have hf := qfactorial_succ q (a-(k+1))
    rw [← hs] at hf
    have hh := ih hka
    rw [hf] at hh
    rw [pow_succ]
    linear_combination -hh

theorem integerQuantumProduct_negative (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (a k : ℕ) (hk : k≤a) :
    integerQuantumProduct q (-(a:ℤ)) k=(-1:ℝ)^k*qfactorial q a/qfactorial q (a-k) := by
  exact (eq_div_iff (qfactorial_ne_zero q hq (a-k))).mpr
    (integerQuantumProduct_negative_cleared q hq hq1 a k hk)

theorem integerQuantumProduct_one (q : ℝ) (hq : 0<q) (hq1 : q≠1) (k : ℕ) :
    integerQuantumProduct q 1 k=qfactorial q k := by
  unfold integerQuantumProduct qfactorial
  apply Finset.prod_congr rfl
  intro j hj
  rw [qnum_eq_qInteger q hq hq1]
  congr 1
  omega

theorem qPochhammer_negative_factorial (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (a k : ℕ) (hk : k≤a) :
    qPochhammer (q^2) (q^(-2*(a:ℤ))) k=
      (q-q⁻¹)^k*q^(-(a:ℤ)*(k:ℤ)+(k.choose 2:ℤ))*qfactorial q a/qfactorial q (a-k) := by
  have he : -2*(a:ℤ)=2*(-(a:ℤ)) := by ring
  rw [he,qPochhammer_symmetric_product q hq hq1,integerQuantumProduct_negative q hq hq1 a k hk]
  have hs : (-(q-q⁻¹))^k*(-1:ℝ)^k=(q-q⁻¹)^k := by rw [← mul_pow];congr 1;ring
  calc
    _ = ((-(q-q⁻¹))^k*(-1:ℝ)^k)*q^(-(a:ℤ)*(k:ℤ)+(k.choose 2:ℤ))*qfactorial q a/qfactorial q (a-k) := by ring
    _ = _ := by rw [hs]

theorem qPochhammer_base_factorial (q : ℝ) (hq : 0<q) (hq1 : q≠1) (k : ℕ) :
    qPochhammer (q^2) (q^2) k=
      (-(q-q⁻¹))^k*q^((k:ℤ)+(k.choose 2:ℤ))*qfactorial q k := by
  have hh := qPochhammer_symmetric_product q hq hq1 1 k
  simpa only [mul_one,one_mul,zpow_ofNat,integerQuantumProduct_one q hq hq1] using hh

end AMSPhysical

#print axioms AMSPhysical.qPochhammer_negative_factorial
#print axioms AMSPhysical.qPochhammer_base_factorial
