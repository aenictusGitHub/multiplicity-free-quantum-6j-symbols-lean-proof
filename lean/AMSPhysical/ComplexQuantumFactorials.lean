import AMSAnalyticRegularity
import Mathlib.Data.Complex.BigOperators
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical
open Set

/-- Finite Laurent-polynomial quantum number; its value at one is regular. -/
def complexQnum (q:ℂ) (n:ℕ):ℂ:=∑ k∈Finset.range n,q^((n:ℤ)-1-2*k)
def complexQfactorial (q:ℂ) (n:ℕ):ℂ:=∏ k∈Finset.range n,complexQnum q (k+1)
def complexQuantumFactorialInt (q:ℂ) (z:ℤ):ℂ:=complexQfactorial q z.toNat

theorem complexQnum_ofReal (q:ℝ) (n:ℕ):complexQnum (q:ℂ) n=(qnum q n:ℂ):=by
  simp only [complexQnum,qnum,Complex.ofReal_sum,Complex.ofReal_zpow]

theorem complexQfactorial_ofReal (q:ℝ) (n:ℕ):complexQfactorial (q:ℂ) n=(qfactorial q n:ℂ):=by
  simp only [complexQfactorial,qfactorial,Complex.ofReal_prod,complexQnum_ofReal]

theorem complexQuantumFactorialInt_ofReal (q:ℝ) (z:ℤ):
    complexQuantumFactorialInt (q:ℂ) z=(quantumFactorialInt q z:ℂ):=
  complexQfactorial_ofReal q z.toNat

theorem complexQnum_analyticAt (q:ℂ) (hq:q≠0) (n:ℕ):AnalyticAt ℂ (fun q:ℂ=>complexQnum q n) q:=by
  unfold complexQnum
  exact (Finset.range n).analyticAt_fun_sum
    (fun k _=>(analyticAt_id:AnalyticAt ℂ (fun q:ℂ=>q) q).fun_zpow hq)

theorem complexQfactorial_analyticAt (q:ℂ) (hq:q≠0) (n:ℕ):
    AnalyticAt ℂ (fun q:ℂ=>complexQfactorial q n) q:=by
  unfold complexQfactorial
  exact (Finset.range n).analyticAt_fun_prod (fun k _=>complexQnum_analyticAt q hq (k+1))

theorem complexQfactorial_at_one (n:ℕ):complexQfactorial 1 n=(qfactorial 1 n:ℂ):=by
  simpa only [Complex.ofReal_one] using complexQfactorial_ofReal 1 n

/-- A concrete local normalization branch, anchored by positive real roots. -/
def complexPositiveRoot (z:ℂ):ℂ:=Complex.exp (Complex.log z/2)

theorem complexPositiveRoot_ofReal (x:ℝ) (hx:0<x):complexPositiveRoot (x:ℂ)=(Real.sqrt x:ℂ):=by
  rw [positive_sqrt_eq_exp x hx,complexPositiveRoot,← Complex.ofReal_log hx.le,
    ← Complex.ofReal_ofNat 2,← Complex.ofReal_div,← Complex.ofReal_exp]

theorem complexPositiveRoot_ne_zero (z:ℂ):complexPositiveRoot z≠0:=Complex.exp_ne_zero _

theorem complexPositiveRoot_sq (z:ℂ) (hz:z≠0):(complexPositiveRoot z)^2=z:=by
  unfold complexPositiveRoot
  rw [sq,← Complex.exp_add]
  have he:Complex.log z/2+Complex.log z/2=Complex.log z:=by ring
  rw [he,Complex.exp_log hz]

theorem complexPositiveRoot_analyticAt (z:ℂ) (hz:z∈Complex.slitPlane):
    AnalyticAt ℂ complexPositiveRoot z:=by
  exact ((analyticAt_clog hz).fun_div analyticAt_const (by norm_num)).cexp

end AMSPhysical
#print axioms AMSPhysical.complexPositiveRoot_ofReal
#print axioms AMSPhysical.complexQfactorial_analyticAt
