import ComplexQuantumFactorials
import PhysicalTypeIINormalization

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical

def complexMixedWeyl (q:ℂ) (h p r:ℕ):ℂ:=mixedWeyl (complexQfactorial q) (complexQnum q) h p r
def complexSameWeyl (q:ℂ) (h p x r:ℕ):ℂ:=sameWeyl (complexQfactorial q) (complexQnum q) h p x r

theorem complexMixedWeyl_ofReal (q:ℝ) (h p r:ℕ):
    complexMixedWeyl (q:ℂ) h p r=((mixedWeyl (qfactorial q) (qnum q) h p r:ℝ):ℂ):=by
  simp only [complexMixedWeyl,mixedWeyl,factorialConstant,complexQnum_ofReal,complexQfactorial_ofReal,
    Complex.ofReal_mul,Complex.ofReal_div]

theorem complexSameWeyl_ofReal (q:ℝ) (h p x r:ℕ):
    complexSameWeyl (q:ℂ) h p x r=((sameWeyl (qfactorial q) (qnum q) h p x r:ℝ):ℂ):=by
  simp only [complexSameWeyl,sameWeyl,factorialConstant,complexQnum_ofReal,complexQfactorial_ofReal,
    Complex.ofReal_mul,Complex.ofReal_div]

theorem complexMixedWeyl_analyticAt (q:ℂ) (hq:q≠0) (hF:∀ n:ℕ,complexQfactorial q n≠0) (h p r:ℕ):
    AnalyticAt ℂ (fun q:ℂ=>complexMixedWeyl q h p r) q:=by
  unfold complexMixedWeyl mixedWeyl factorialConstant
  exact (((complexQnum_analyticAt q hq (p+r+h+1)).mul
    (complexQfactorial_analyticAt q hq (p+h))).mul (complexQfactorial_analyticAt q hq (r+h))).fun_div
    (((complexQfactorial_analyticAt q hq p).mul (complexQfactorial_analyticAt q hq r)).mul
      ((complexQfactorial_analyticAt q hq (h+1)).mul (complexQfactorial_analyticAt q hq h)))
    (mul_ne_zero (mul_ne_zero (hF _) (hF _)) (mul_ne_zero (hF _) (hF _)))

theorem complexSameWeyl_analyticAt (q:ℂ) (hq:q≠0) (hF:∀ n:ℕ,complexQfactorial q n≠0) (h p x r:ℕ):
    AnalyticAt ℂ (fun q:ℂ=>complexSameWeyl q h p x r) q:=by
  unfold complexSameWeyl sameWeyl factorialConstant
  exact (((complexQnum_analyticAt q hq (p+x+1)).mul
    (complexQfactorial_analyticAt q hq (p+x+r+h+1))).mul (complexQfactorial_analyticAt q hq (r+h))).fun_div
    (((complexQfactorial_analyticAt q hq (p+x+r+1)).mul (complexQfactorial_analyticAt q hq r)).mul
      ((complexQfactorial_analyticAt q hq (h+1)).mul (complexQfactorial_analyticAt q hq h)))
    (mul_ne_zero (mul_ne_zero (hF _) (hF _)) (mul_ne_zero (hF _) (hF _)))

end AMSPhysical
#print axioms AMSPhysical.complexMixedWeyl_analyticAt
