import ComplexQuantumFactorials

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
noncomputable section
namespace AMSPhysical

def complexThetaSq (q:ℂ) (h:ℕ) (a b c:ℤ):ℂ:=
  complexQuantumFactorialInt q ((a+b-c)/2)*complexQuantumFactorialInt q ((a+c-b)/2)*
    complexQuantumFactorialInt q ((b+c-a)/2)/complexQuantumFactorialInt q ((a+b+c)/2+h+1)

def complexFourTriangleRadicand (q:ℂ) (h:ℕ) (a b c d i j:ℤ):ℂ:=
  complexThetaSq q h a b i*complexThetaSq q h c d i*complexThetaSq q h a d j*complexThetaSq q h b c j

def complexAMSExpression (q:ℂ) (h:ℕ) (typeII:Bool) (a b c d i j:ℤ):ℂ:=
  complexQfactorial q (h+1)*complexQfactorial q h*complexPositiveRoot (complexFourTriangleRadicand q h a b c d i j)*
    AMSGeneral.kernel (complexQuantumFactorialInt q) h typeII a b c d i j

theorem complexThetaSq_ofReal (q:ℝ) (h:ℕ) (a b c:ℤ):
    complexThetaSq (q:ℂ) h a b c=(amsThetaSq q h a b c:ℂ):=by
  simp only [complexThetaSq,amsThetaSq,complexQuantumFactorialInt_ofReal,Complex.ofReal_mul,Complex.ofReal_div]

theorem complexFourTriangleRadicand_ofReal (q:ℝ) (h:ℕ) (a b c d i j:ℤ):
    complexFourTriangleRadicand (q:ℂ) h a b c d i j=
      ((amsThetaSq q h a b i*amsThetaSq q h c d i*amsThetaSq q h a d j*amsThetaSq q h b c j:ℝ):ℂ):=by
  simp only [complexFourTriangleRadicand,complexThetaSq_ofReal,Complex.ofReal_mul]

theorem complexAMSKernel_ofReal (q:ℝ) (h:ℕ) (typeII:Bool) (a b c d i j:ℤ):
    AMSGeneral.kernel (complexQuantumFactorialInt (q:ℂ)) h typeII a b c d i j=
      ((AMSGeneral.kernel (quantumFactorialInt q) h typeII a b c d i j:ℝ):ℂ):=by
  simp only [AMSGeneral.kernel,AMSGeneral.series,complexQuantumFactorialInt_ofReal,
    Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_zpow,
    Complex.ofReal_neg,Complex.ofReal_one]

theorem complexAMSExpression_ofReal (q:ℝ) (hq:0<q) (h:ℕ) (typeII:Bool) (a b c d i j:ℤ):
    complexAMSExpression (q:ℂ) h typeII a b c d i j=
      ((amsFourTrianglePrefactor q h a b c d i j*
        AMSGeneral.kernel (quantumFactorialInt q) h typeII a b c d i j:ℝ):ℂ):=by
  unfold complexAMSExpression
  rw [complexFourTriangleRadicand_ofReal,complexPositiveRoot_ofReal _
    (mul_pos (mul_pos (mul_pos (amsThetaSq_pos q hq h a b i) (amsThetaSq_pos q hq h c d i))
      (amsThetaSq_pos q hq h a d j)) (amsThetaSq_pos q hq h b c j)),complexAMSKernel_ofReal]
  simp only [complexQfactorial_ofReal,amsFourTrianglePrefactor,factorialConstant,Complex.ofReal_mul]

theorem complexThetaSq_analyticAt (q:ℂ) (hq:q≠0) (hF:∀ n:ℕ,complexQfactorial q n≠0)
    (h:ℕ) (a b c:ℤ):AnalyticAt ℂ (fun q:ℂ=>complexThetaSq q h a b c) q:=by
  unfold complexThetaSq complexQuantumFactorialInt
  exact (((complexQfactorial_analyticAt q hq _).mul (complexQfactorial_analyticAt q hq _)).mul
    (complexQfactorial_analyticAt q hq _)).fun_div (complexQfactorial_analyticAt q hq _) (hF _)

theorem complexFourTriangleRadicand_analyticAt (q:ℂ) (hq:q≠0) (hF:∀ n:ℕ,complexQfactorial q n≠0)
    (h:ℕ) (a b c d i j:ℤ):AnalyticAt ℂ (fun q:ℂ=>complexFourTriangleRadicand q h a b c d i j) q:=
  (((complexThetaSq_analyticAt q hq hF h a b i).mul (complexThetaSq_analyticAt q hq hF h c d i)).mul
    (complexThetaSq_analyticAt q hq hF h a d j)).mul (complexThetaSq_analyticAt q hq hF h b c j)

theorem complexAMSKernel_analyticAt (q:ℂ) (hq:q≠0) (hF:∀ n:ℕ,complexQfactorial q n≠0)
    (h:ℕ) (typeII:Bool) (a b c d i j:ℤ):
    AnalyticAt ℂ (fun q:ℂ=>AMSGeneral.kernel (complexQuantumFactorialInt q) h typeII a b c d i j) q:=by
  unfold AMSGeneral.kernel AMSGeneral.series
  apply Finset.analyticAt_fun_sum
  intro u hu
  apply AnalyticAt.fun_div
  · exact analyticAt_const.mul (complexQfactorial_analyticAt q hq _)
  · exact ((((((complexQfactorial_analyticAt q hq _).mul (complexQfactorial_analyticAt q hq _)).mul
      (complexQfactorial_analyticAt q hq _)).mul (complexQfactorial_analyticAt q hq _)).mul
      (complexQfactorial_analyticAt q hq _)).mul (complexQfactorial_analyticAt q hq _)).mul
      (complexQfactorial_analyticAt q hq _)
  · repeat' apply mul_ne_zero
    all_goals exact hF _

theorem complexAMSExpression_analyticAt (q:ℂ) (hq:q≠0) (hF:∀ n:ℕ,complexQfactorial q n≠0)
    (h:ℕ) (typeII:Bool) (a b c d i j:ℤ)
    (hR:complexFourTriangleRadicand q h a b c d i j∈Complex.slitPlane):
    AnalyticAt ℂ (fun q:ℂ=>complexAMSExpression q h typeII a b c d i j) q:=by
  have hS:AnalyticAt ℂ (fun q:ℂ=>complexPositiveRoot (complexFourTriangleRadicand q h a b c d i j)) q:=
    (complexPositiveRoot_analyticAt _ hR).comp
      (f:=fun q:ℂ=>complexFourTriangleRadicand q h a b c d i j) (x:=q)
      (complexFourTriangleRadicand_analyticAt q hq hF h a b c d i j)
  exact (((complexQfactorial_analyticAt q hq (h+1)).mul (complexQfactorial_analyticAt q hq h)).mul hS).mul
    (complexAMSKernel_analyticAt q hq hF h typeII a b c d i j)

theorem complexAMSExpression_analyticAt_positive (q:ℝ) (hq:0<q)
    (h:ℕ) (typeII:Bool) (a b c d i j:ℤ):
    AnalyticAt ℂ (fun z:ℂ=>complexAMSExpression z h typeII a b c d i j) (q:ℂ):=by
  apply complexAMSExpression_analyticAt q (Complex.ofReal_ne_zero.mpr (ne_of_gt hq))
    (fun n=>by rw [complexQfactorial_ofReal];exact Complex.ofReal_ne_zero.mpr (qfactorial_ne_zero q hq n))
  rw [complexFourTriangleRadicand_ofReal,Complex.ofReal_mem_slitPlane]
  exact mul_pos (mul_pos (mul_pos (amsThetaSq_pos q hq h a b i) (amsThetaSq_pos q hq h c d i))
    (amsThetaSq_pos q hq h a d j)) (amsThetaSq_pos q hq h b c j)

end AMSPhysical
#print axioms AMSPhysical.complexAMSExpression_analyticAt_positive
