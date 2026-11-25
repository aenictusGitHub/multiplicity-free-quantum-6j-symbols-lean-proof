import ComplexClebschCoefficients

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
noncomputable section
namespace AMSPhysical

theorem complexCouplingNormClosed_analyticAt (q:ℂ) (hq:q≠0)
    (hF:∀ n:ℕ,complexQfactorial q n≠0) (a b r:ℕ):
    AnalyticAt ℂ (fun q:ℂ=>complexCouplingNormClosed q a b r) q:=by
  unfold complexCouplingNormClosed
  exact (((((analyticAt_id:AnalyticAt ℂ (fun q:ℂ=>q) q).fun_zpow hq).mul
    (complexQfactorial_analyticAt q hq r)).mul (complexQfactorial_analyticAt q hq a)).mul
    (complexQfactorial_analyticAt q hq b)).mul (complexQfactorial_analyticAt q hq (a+b+r+1)) |>.fun_div
      (((complexQfactorial_analyticAt q hq (a+r)).mul (complexQfactorial_analyticAt q hq (b+r))).mul
        (complexQfactorial_analyticAt q hq (a+b+1)))
      (mul_ne_zero (mul_ne_zero (hF _) (hF _)) (hF _))

theorem complexClebschFactorialTerm_analyticAt (q:ℂ) (hq:q≠0)
    (hF:∀ n:ℕ,complexQfactorial q n≠0) (l m r a u k:ℕ):
    AnalyticAt ℂ (fun q:ℂ=>complexClebschFactorialTerm q l m r a u k) q:=by
  unfold complexClebschFactorialTerm
  exact (((analyticAt_const.mul
    ((analyticAt_id:AnalyticAt ℂ (fun q:ℂ=>q) q).fun_zpow hq)).mul
      (complexQfactorial_analyticAt q hq (l-k))).mul
      (complexQfactorial_analyticAt q hq (m-r+k))).fun_div
    ((((complexQfactorial_analyticAt q hq k).mul (complexQfactorial_analyticAt q hq (r-k))).mul
      (complexQfactorial_analyticAt q hq (descendantIndex a k u))).mul
      (complexQfactorial_analyticAt q hq (a-descendantIndex a k u)))
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (hF _) (hF _)) (hF _)) (hF _))

theorem complexClebschFactorialSum_analyticAt (q:ℂ) (hq:q≠0)
    (hF:∀ n:ℕ,complexQfactorial q n≠0) (l m r a u:ℕ):
    AnalyticAt ℂ (fun q:ℂ=>complexClebschFactorialSum q l m r a u) q:=by
  unfold complexClebschFactorialSum
  apply Finset.analyticAt_fun_sum
  intro k hk
  by_cases h:DescendantAdmissible a k u
  · simp only [if_pos h]
    exact complexClebschFactorialTerm_analyticAt q hq hF l m r a u k
  · simp only [if_neg h]
    exact analyticAt_const

theorem complexRegularClebschCoefficient_analyticAt (q:ℂ) (hq:q≠0)
    (hF:∀ n:ℕ,complexQfactorial q n≠0) (l m r a u v:ℕ)
    (hN:complexCouplingNormClosed q (l-r) (m-r) r∈Complex.slitPlane):
    AnalyticAt ℂ (fun q:ℂ=>complexRegularClebschCoefficient q l m r a u v) q:=by
  have hR:AnalyticAt ℂ (fun q:ℂ=>complexPositiveRoot (complexCouplingNormClosed q (l-r) (m-r) r)) q:=
    (complexPositiveRoot_analyticAt _ hN).comp
      (f:=fun q:ℂ=>complexCouplingNormClosed q (l-r) (m-r) r) (x:=q)
      (complexCouplingNormClosed_analyticAt q hq hF _ _ _)
  have hRi:=hR.fun_inv (complexPositiveRoot_ne_zero _)
  unfold complexRegularClebschCoefficient
  exact (((((hRi.mul
    ((analyticAt_id:AnalyticAt ℂ (fun q:ℂ=>q) q).fun_zpow hq)).mul
      (complexQfactorial_analyticAt q hq r)).mul (complexQfactorial_analyticAt q hq a)).mul
      (complexQfactorial_analyticAt q hq (coupledLabel l m r-a))).fun_div
    (((complexQfactorial_analyticAt q hq (coupledLabel l m r)).mul
      (complexQfactorial_analyticAt q hq (l-u))).mul (complexQfactorial_analyticAt q hq (m-v)))
    (mul_ne_zero (mul_ne_zero (hF _) (hF _)) (hF _))).mul
      (complexClebschFactorialSum_analyticAt q hq hF l m r a u)

theorem complexClebschCoefficient_analyticAt (q:ℂ) (hq:q≠0)
    (hF:∀ n:ℕ,complexQfactorial q n≠0) (l m r a u v:ℕ)
    (hN:complexCouplingNormClosed q (l-r) (m-r) r∈Complex.slitPlane):
    AnalyticAt ℂ (fun q:ℂ=>complexClebschCoefficient q l m r a u v) q:=by
  unfold complexClebschCoefficient
  by_cases h:u+v=r+a
  · simp only [if_pos h]
    exact complexRegularClebschCoefficient_analyticAt q hq hF l m r a u v hN
  · simp only [if_neg h]
    exact analyticAt_const

theorem complexQfactorial_ofReal_ne_zero (q:ℝ) (hq:0<q) (n:ℕ):complexQfactorial (q:ℂ) n≠0:=by
  rw [complexQfactorial_ofReal]
  exact Complex.ofReal_ne_zero.mpr (qfactorial_ne_zero q hq n)

theorem complexCouplingNormClosed_ofReal_slitPlane (q:ℝ) (hq:0<q) (a b r:ℕ):
    complexCouplingNormClosed (q:ℂ) a b r∈Complex.slitPlane:=by
  rw [complexCouplingNormClosed_ofReal,Complex.ofReal_mem_slitPlane]
  exact couplingNormClosed_pos q hq a b r

/-- Independent complex CG coefficients are holomorphic near every positive
real parameter, including one. -/
theorem complexClebschCoefficient_analyticAt_positive (q:ℝ) (hq:0<q) (l m r a u v:ℕ):
    AnalyticAt ℂ (fun z:ℂ=>complexClebschCoefficient z l m r a u v) (q:ℂ):=
  complexClebschCoefficient_analyticAt q (Complex.ofReal_ne_zero.mpr (ne_of_gt hq))
    (complexQfactorial_ofReal_ne_zero q hq) l m r a u v
    (complexCouplingNormClosed_ofReal_slitPlane q hq _ _ _)

end AMSPhysical
#print axioms AMSPhysical.complexClebschCoefficient_analyticAt_positive
