import QuantumClebschFactorial
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
open Set
open scoped Topology

theorem positive_sqrt_eq_exp (x : ℝ) (hx : 0<x) : Real.sqrt x=Real.exp (Real.log x/2) := by
  rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos hx]
  congr 1
  ring

theorem positive_sqrt_analyticAt (x : ℝ) (hx : 0<x) : AnalyticAt ℝ Real.sqrt x := by
  have hlog : AnalyticAt ℝ (fun y : ℝ => Real.log y/2) x :=
    (analyticAt_log hx).fun_div analyticAt_const (by norm_num)
  have he : AnalyticAt ℝ (fun y : ℝ => Real.exp (Real.log y/2)) x := hlog.rexp'
  apply he.congr
  filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
  exact (positive_sqrt_eq_exp y hy).symm

theorem qfactorial_analytic (n : ℕ) : AnalyticOnNhd ℝ (fun q : ℝ => qfactorial q n) (Ioi 0) := by
  intro q hq
  unfold qfactorial
  exact (Finset.range n).analyticAt_fun_prod (fun k _ => qnum_analytic (k+1) q hq)

theorem couplingNormClosed_pos (q : ℝ) (hq : 0<q) (a b r : ℕ) : 0<couplingNormClosed q a b r := by
  unfold couplingNormClosed
  exact div_pos
    (mul_pos (mul_pos (mul_pos (mul_pos (zpow_pos hq _) (qfactorial_pos q hq r))
      (qfactorial_pos q hq a)) (qfactorial_pos q hq b)) (qfactorial_pos q hq (a+b+r+1)))
    (mul_pos (mul_pos (qfactorial_pos q hq (a+r)) (qfactorial_pos q hq (b+r))) (qfactorial_pos q hq (a+b+1)))

theorem couplingNormClosed_analytic (a b r : ℕ) :
    AnalyticOnNhd ℝ (fun q : ℝ => couplingNormClosed q a b r) (Ioi 0) := by
  intro q hq
  unfold couplingNormClosed
  exact (((((analyticAt_id : AnalyticAt ℝ (fun x : ℝ => x) q).fun_zpow (ne_of_gt hq)).mul
    (qfactorial_analytic r q hq)).mul (qfactorial_analytic a q hq)).mul (qfactorial_analytic b q hq)).mul
    (qfactorial_analytic (a+b+r+1) q hq) |>.fun_div
      (((qfactorial_analytic (a+r) q hq).mul (qfactorial_analytic (b+r) q hq)).mul
        (qfactorial_analytic (a+b+1) q hq))
      (mul_ne_zero (mul_ne_zero (qfactorial_ne_zero q hq (a+r)) (qfactorial_ne_zero q hq (b+r)))
        (qfactorial_ne_zero q hq (a+b+1)))

theorem clebschFactorialTerm_analytic (l m r a u k : ℕ) :
    AnalyticOnNhd ℝ (fun q : ℝ => clebschFactorialTerm q l m r a u k) (Ioi 0) := by
  intro q hq
  unfold clebschFactorialTerm
  exact (((analyticAt_const.mul
    ((analyticAt_id : AnalyticAt ℝ (fun x : ℝ => x) q).fun_zpow (ne_of_gt hq))).mul
    (qfactorial_analytic (l-k) q hq)).mul (qfactorial_analytic (m-r+k) q hq)).fun_div
    ((((qfactorial_analytic k q hq).mul (qfactorial_analytic (r-k) q hq)).mul
      (qfactorial_analytic (descendantIndex a k u) q hq)).mul
      (qfactorial_analytic (a-descendantIndex a k u) q hq))
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (qfactorial_ne_zero q hq k) (qfactorial_ne_zero q hq (r-k)))
      (qfactorial_ne_zero q hq (descendantIndex a k u)))
      (qfactorial_ne_zero q hq (a-descendantIndex a k u)))

theorem clebschFactorialSum_analytic (l m r a u : ℕ) :
    AnalyticOnNhd ℝ (fun q : ℝ => clebschFactorialSum q l m r a u) (Ioi 0) := by
  intro q hq
  unfold clebschFactorialSum
  apply (Finset.range (r+1)).analyticAt_fun_sum
  intro k hk
  by_cases hadm : DescendantAdmissible a k u
  · simp only [if_pos hadm]
    exact clebschFactorialTerm_analytic l m r a u k q hq
  · simp only [if_neg hadm]
    exact analyticAt_const

/-- The actual CG coefficient formula has an analytic continuation through q=1. -/
theorem regularClebschFactorialCoefficient_analytic (l m r a u v : ℕ) :
    AnalyticOnNhd ℝ (fun q : ℝ => regularClebschFactorialCoefficient q l m r a u v) (Ioi 0) := by
  intro q hq
  have hN := couplingNormClosed_analytic (l-r) (m-r) r q hq
  have hNp := couplingNormClosed_pos q hq (l-r) (m-r) r
  have hS : AnalyticAt ℝ (fun x : ℝ => Real.sqrt (couplingNormClosed x (l-r) (m-r) r)) q :=
    (positive_sqrt_analyticAt _ hNp).comp
      (f:=fun x : ℝ => couplingNormClosed x (l-r) (m-r) r) (x:=q) hN
  have hSi := hS.fun_inv (ne_of_gt (Real.sqrt_pos.mpr hNp))
  unfold regularClebschFactorialCoefficient
  exact (((((hSi.mul
    ((analyticAt_id : AnalyticAt ℝ (fun x : ℝ => x) q).fun_zpow (ne_of_gt hq))).mul
    (qfactorial_analytic r q hq)).mul (qfactorial_analytic a q hq)).mul
    (qfactorial_analytic (coupledLabel l m r-a) q hq)).fun_div
    (((qfactorial_analytic (coupledLabel l m r) q hq).mul (qfactorial_analytic (l-u) q hq)).mul
      (qfactorial_analytic (m-v) q hq))
    (mul_ne_zero (mul_ne_zero (qfactorial_ne_zero q hq (coupledLabel l m r)) (qfactorial_ne_zero q hq (l-u)))
      (qfactorial_ne_zero q hq (m-v)))).mul (clebschFactorialSum_analytic l m r a u q hq)

end AMSPhysical

#print axioms AMSPhysical.regularClebschFactorialCoefficient_analytic
