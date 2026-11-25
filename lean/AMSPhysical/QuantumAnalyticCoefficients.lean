import QuantumClebschClosed
import QuantumPositive
import AnalyticSign

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical
open Set

theorem qnum_analytic (n : ℕ) : AnalyticOnNhd ℝ (fun q : ℝ => qnum q n) (Ioi 0) := by
  intro q hq
  unfold qnum
  exact (Finset.range n).analyticAt_fun_sum
    (fun k _ => (analyticAt_id : AnalyticAt ℝ (fun x : ℝ => x) q).fun_zpow (ne_of_gt hq))

def regularCouplingCoefficient (m : ℤ) (r : ℕ) : ℕ → ℝ → ℝ
  | 0 => fun _ => 1
  | k+1 => fun q => -(regularCouplingCoefficient m r k q*qnum q (r-k))/
      (qnum q (k+1)*q^(m-2*((r:ℤ)-k-1)))

/-- The actual highest-weight coefficients admit an analytic extension through q=1. -/
theorem regularCouplingCoefficient_analytic (m : ℤ) (r k : ℕ) :
    AnalyticOnNhd ℝ (regularCouplingCoefficient m r k) (Ioi 0) := by
  induction k with
  | zero => exact analyticOnNhd_const
  | succ k ih =>
    intro q hq
    exact ((ih q hq).mul (qnum_analytic (r-k) q hq)).neg.fun_div
      ((qnum_analytic (k+1) q hq).mul
        ((analyticAt_id : AnalyticAt ℝ (fun x : ℝ => x) q).fun_zpow (ne_of_gt hq)))
      (mul_ne_zero (ne_of_gt (qnum_pos q hq (k+1) (by omega))) (zpow_ne_zero _ (ne_of_gt hq)))

theorem qnum_eq_qInteger (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) :
    qnum q n=qInteger q (n:ℤ) := by
  rw [qnum_eq_standard q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)]
  simp only [qInteger,zpow_natCast]

theorem regularCouplingCoefficient_eq (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (m : ℤ) (r k : ℕ) (hk : k≤r) :
    regularCouplingCoefficient m r k q=couplingCoefficient q m r k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [regularCouplingCoefficient,couplingCoefficient,ih (by omega),qnum_eq_qInteger q hq hq1]
    have he : ((r-k:ℕ):ℤ)=(r:ℤ)-k := Int.natCast_sub (by omega)
    rw [he]

theorem regularCouplingCoefficient_at_one (m : ℤ) (r k : ℕ) :
    regularCouplingCoefficient m r k 1=(-1:ℝ)^k*(r.choose k:ℝ) := by
  induction k with
  | zero => simp [regularCouplingCoefficient]
  | succ k ih =>
    simp only [regularCouplingCoefficient,ih,qnum_one,one_zpow,mul_one,pow_succ]
    have hc : (r.choose (k+1):ℝ)*(k+1)=(r.choose k:ℝ)*(r-k:ℕ) := by
      exact_mod_cast Nat.choose_succ_right_eq r k
    simp only [Nat.cast_add,Nat.cast_one] at *
    apply (div_eq_iff (by positivity : (k+1:ℝ)≠0)).mpr
    linear_combination ((-1:ℝ)^k)*hc

end AMSPhysical

#print axioms AMSPhysical.regularCouplingCoefficient_analytic
#print axioms AMSPhysical.regularCouplingCoefficient_at_one
