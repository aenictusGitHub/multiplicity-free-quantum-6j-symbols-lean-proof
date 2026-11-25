import ComplexRacahOverlap

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
noncomputable section
namespace AMSPhysical

theorem complexCouplingCoefficient_analyticAt (q:ℂ) (hq:q≠0)
    (hF:∀ n:ℕ,complexQfactorial q n≠0) (m:ℤ) (r k:ℕ):
    AnalyticAt ℂ (fun q:ℂ=>complexCouplingCoefficient q m r k) q:=by
  unfold complexCouplingCoefficient
  exact ((analyticAt_const.mul
    ((analyticAt_id:AnalyticAt ℂ (fun q:ℂ=>q) q).fun_zpow hq)).mul
      (complexQfactorial_analyticAt q hq r)).fun_div
      ((complexQfactorial_analyticAt q hq k).mul (complexQfactorial_analyticAt q hq (r-k)))
      (mul_ne_zero (hF _) (hF _))

theorem complexLeftTreeCoefficient_analyticAt (q:ℂ) (hq:q≠0)
    (hF:∀ n:ℕ,complexQfactorial q n≠0) (l m n:ℕ) (p:LeftHighestPath l m n)
    (hI:complexCouplingNormClosed q (l-p.1.val) (m-p.1.val) p.1.val∈Complex.slitPlane)
    (hO:complexCouplingNormClosed q (coupledLabel l m p.1-p.2.val) (n-p.2.val) p.2.val∈Complex.slitPlane)
    (i:Fin (l+1)) (j:Fin (m+1)) (k:Fin (n+1)):
    AnalyticAt ℂ (fun q:ℂ=>complexLeftTreeCoefficient q l m n p i j k) q:=by
  have hR:AnalyticAt ℂ (fun q:ℂ=>complexPositiveRoot (complexCouplingNormClosed q
      (coupledLabel l m p.1-p.2.val) (n-p.2.val) p.2.val)) q:=
    (complexPositiveRoot_analyticAt _ hO).comp
      (f:=fun q:ℂ=>complexCouplingNormClosed q (coupledLabel l m p.1-p.2.val) (n-p.2.val) p.2.val)
      (x:=q) (complexCouplingNormClosed_analyticAt q hq hF _ _ _)
  unfold complexLeftTreeCoefficient
  apply (hR.fun_inv (complexPositiveRoot_ne_zero _)).mul
  apply Finset.analyticAt_fun_sum
  intro t ht
  exact ((complexCouplingCoefficient_analyticAt q hq hF _ _ _).mul
    (complexClebschCoefficient_analyticAt q hq hF l m p.1.val (leftRootIndexPair l m n p t).1.val i.val j.val hI)).mul
      analyticAt_const

theorem complexRightTreeCoefficient_analyticAt (q:ℂ) (hq:q≠0)
    (hF:∀ n:ℕ,complexQfactorial q n≠0) (l m n:ℕ) (p:RightHighestPath l m n)
    (hI:complexCouplingNormClosed q (m-p.1.val) (n-p.1.val) p.1.val∈Complex.slitPlane)
    (hO:complexCouplingNormClosed q (l-p.2.val) (coupledLabel m n p.1-p.2.val) p.2.val∈Complex.slitPlane)
    (i:Fin (l+1)) (j:Fin (m+1)) (k:Fin (n+1)):
    AnalyticAt ℂ (fun q:ℂ=>complexRightTreeCoefficient q l m n p i j k) q:=by
  have hR:AnalyticAt ℂ (fun q:ℂ=>complexPositiveRoot (complexCouplingNormClosed q
      (l-p.2.val) (coupledLabel m n p.1-p.2.val) p.2.val)) q:=
    (complexPositiveRoot_analyticAt _ hO).comp
      (f:=fun q:ℂ=>complexCouplingNormClosed q (l-p.2.val) (coupledLabel m n p.1-p.2.val) p.2.val)
      (x:=q) (complexCouplingNormClosed_analyticAt q hq hF _ _ _)
  unfold complexRightTreeCoefficient
  apply (hR.fun_inv (complexPositiveRoot_ne_zero _)).mul
  apply Finset.analyticAt_fun_sum
  intro t ht
  exact ((complexCouplingCoefficient_analyticAt q hq hF _ _ _).mul analyticAt_const).mul
    (complexClebschCoefficient_analyticAt q hq hF m n p.1.val (rightRootIndexPair l m n p t).2.val j.val k.val hI)

theorem complexQuantumWeight_analyticAt (q:ℂ) (hq:q≠0)
    (hF:∀ n:ℕ,complexQfactorial q n≠0) (L k:ℕ):
    AnalyticAt ℂ (fun q:ℂ=>complexQuantumWeight q L k) q:=by
  unfold complexQuantumWeight
  exact ((((analyticAt_id:AnalyticAt ℂ (fun q:ℂ=>q) q).fun_zpow hq).mul
    (complexQfactorial_analyticAt q hq k)).mul (complexQfactorial_analyticAt q hq (L-k))).fun_div
    (complexQfactorial_analyticAt q hq L) (hF L)

theorem complexRacahOverlap_analyticAt (q:ℂ) (hq:q≠0)
    (hF:∀ n:ℕ,complexQfactorial q n≠0) (l m n:ℕ) (p:LeftHighestPath l m n) (a:RightHighestPath l m n)
    (hLI:complexCouplingNormClosed q (l-p.1.val) (m-p.1.val) p.1.val∈Complex.slitPlane)
    (hLO:complexCouplingNormClosed q (coupledLabel l m p.1-p.2.val) (n-p.2.val) p.2.val∈Complex.slitPlane)
    (hRI:complexCouplingNormClosed q (m-a.1.val) (n-a.1.val) a.1.val∈Complex.slitPlane)
    (hRO:complexCouplingNormClosed q (l-a.2.val) (coupledLabel m n a.1-a.2.val) a.2.val∈Complex.slitPlane):
    AnalyticAt ℂ (fun q:ℂ=>complexRacahOverlap q l m n p a) q:=by
  unfold complexRacahOverlap
  apply Finset.analyticAt_fun_sum
  intro i hi
  apply Finset.analyticAt_fun_sum
  intro j hj
  apply Finset.analyticAt_fun_sum
  intro k hk
  exact ((((complexQuantumWeight_analyticAt q hq hF l i.val).mul
    (complexQuantumWeight_analyticAt q hq hF m j.val)).mul
    (complexQuantumWeight_analyticAt q hq hF n k.val)).mul
    (complexLeftTreeCoefficient_analyticAt q hq hF l m n p hLI hLO i j k)).mul
    (complexRightTreeCoefficient_analyticAt q hq hF l m n a hRI hRO i j k)

/-- Holomorphic independent recoupling overlap near every positive real q,
including the classical point q=1. -/
theorem complexRacahOverlap_analyticAt_positive (q:ℝ) (hq:0<q) (l m n:ℕ)
    (p:LeftHighestPath l m n) (a:RightHighestPath l m n):
    AnalyticAt ℂ (fun z:ℂ=>complexRacahOverlap z l m n p a) (q:ℂ):=
  complexRacahOverlap_analyticAt q (Complex.ofReal_ne_zero.mpr (ne_of_gt hq))
    (complexQfactorial_ofReal_ne_zero q hq) l m n p a
    (complexCouplingNormClosed_ofReal_slitPlane q hq _ _ _)
    (complexCouplingNormClosed_ofReal_slitPlane q hq _ _ _)
    (complexCouplingNormClosed_ofReal_slitPlane q hq _ _ _)
    (complexCouplingNormClosed_ofReal_slitPlane q hq _ _ _)

end AMSPhysical
#print axioms AMSPhysical.complexRacahOverlap_analyticAt_positive
