import AMSTriangleCoordinates
import QuantumClebschAnalytic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
open Set

theorem quantumFactorialInt_pos (q:ℝ) (hq:0<q) (z:ℤ):0<quantumFactorialInt q z:=
  qfactorial_pos q hq z.toNat

theorem quantumFactorialInt_analytic (z:ℤ):
    AnalyticOnNhd ℝ (fun q:ℝ=>quantumFactorialInt q z) (Ioi 0):=
  qfactorial_analytic z.toNat

theorem amsThetaSq_pos (q:ℝ) (hq:0<q) (h:ℕ) (a b c:ℤ):0<amsThetaSq q h a b c:=
  div_pos (mul_pos (mul_pos (quantumFactorialInt_pos q hq _) (quantumFactorialInt_pos q hq _))
    (quantumFactorialInt_pos q hq _)) (quantumFactorialInt_pos q hq _)

theorem amsThetaSq_analytic (h:ℕ) (a b c:ℤ):
    AnalyticOnNhd ℝ (fun q:ℝ=>amsThetaSq q h a b c) (Ioi 0):=by
  intro q hq
  exact (((quantumFactorialInt_analytic ((a+b-c)/2) q hq).mul
    (quantumFactorialInt_analytic ((a+c-b)/2) q hq)).mul
    (quantumFactorialInt_analytic ((b+c-a)/2) q hq)).fun_div
    (quantumFactorialInt_analytic ((a+b+c)/2+h+1) q hq)
    (ne_of_gt (quantumFactorialInt_pos q hq _))

theorem amsFourTrianglePrefactor_analytic (h:ℕ) (a b c d i j:ℤ):
    AnalyticOnNhd ℝ (fun q:ℝ=>amsFourTrianglePrefactor q h a b c d i j) (Ioi 0):=by
  intro q hq
  have hp:=mul_pos (mul_pos (mul_pos (amsThetaSq_pos q hq h a b i)
    (amsThetaSq_pos q hq h c d i)) (amsThetaSq_pos q hq h a d j)) (amsThetaSq_pos q hq h b c j)
  have hA:=(((amsThetaSq_analytic h a b i q hq).mul (amsThetaSq_analytic h c d i q hq)).mul
    (amsThetaSq_analytic h a d j q hq)).mul (amsThetaSq_analytic h b c j q hq)
  have hS:AnalyticAt ℝ (fun q:ℝ=>Real.sqrt
      (amsThetaSq q h a b i*amsThetaSq q h c d i*amsThetaSq q h a d j*amsThetaSq q h b c j)) q:=
    (positive_sqrt_analyticAt _ hp).comp
      (f:=fun x:ℝ=>amsThetaSq x h a b i*amsThetaSq x h c d i*amsThetaSq x h a d j*amsThetaSq x h b c j)
      (x:=q) hA
  exact ((qfactorial_analytic (h+1) q hq).mul (qfactorial_analytic h q hq)).mul hS

theorem amsKernel_analytic (h:ℕ) (typeII:Bool) (a b c d i j:ℤ):
    AnalyticOnNhd ℝ (fun q:ℝ=>AMSGeneral.kernel (quantumFactorialInt q) h typeII a b c d i j) (Ioi 0):=by
  intro q hq
  unfold AMSGeneral.kernel AMSGeneral.series
  apply Finset.analyticAt_fun_sum
  intro u hu
  apply AnalyticAt.fun_div
  · exact analyticAt_const.mul (quantumFactorialInt_analytic _ q hq)
  · exact ((((((quantumFactorialInt_analytic _ q hq).mul (quantumFactorialInt_analytic _ q hq)).mul
      (quantumFactorialInt_analytic _ q hq)).mul (quantumFactorialInt_analytic _ q hq)).mul
      (quantumFactorialInt_analytic _ q hq)).mul (quantumFactorialInt_analytic _ q hq)).mul
      (quantumFactorialInt_analytic _ q hq)
  · repeat' apply mul_ne_zero
    all_goals exact ne_of_gt (quantumFactorialInt_pos q hq _)

/-- The complete literal AMS expression is analytic through q=1. This is
regularity of the established expression, not a definition of a physical
coefficient by that expression. -/
theorem amsExpression_analytic (h:ℕ) (typeII:Bool) (a b c d i j:ℤ):
    AnalyticOnNhd ℝ (fun q:ℝ=>amsFourTrianglePrefactor q h a b c d i j*
      AMSGeneral.kernel (quantumFactorialInt q) h typeII a b c d i j) (Ioi 0):=
  (amsFourTrianglePrefactor_analytic h a b c d i j).mul (amsKernel_analytic h typeII a b c d i j)

theorem qfactorial_at_one (n:ℕ):qfactorial 1 n=(n.factorial:ℝ):=by
  induction n with
  | zero=>simp only [qfactorial_zero,Nat.factorial_zero,Nat.cast_one]
  | succ n ih=>
    rw [qfactorial_succ,ih,qnum_one,Nat.factorial_succ,Nat.cast_mul]
    ring

theorem quantumFactorialInt_at_one (z:ℤ):quantumFactorialInt 1 z=(z.toNat.factorial:ℝ):=
  qfactorial_at_one z.toNat

end AMSPhysical
#print axioms AMSPhysical.amsExpression_analytic
