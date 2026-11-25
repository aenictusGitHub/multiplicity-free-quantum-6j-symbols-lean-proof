import GlobalCupBoundaryTransport

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1200000
noncomputable section
namespace AMSPhysical

def cupHighestFirstBoundaryEval (q : ℝ) (n l m h c : ℕ) : quantumCupSpan q n l m h c →ₗ[ℝ] ℝ :=
  (Finsupp.lapply (quantumCupBoundaryPoint n (l:ℤ) (h:ℤ) (c:ℤ) 0 m)).comp
    (quantumCupSpan q n l m h c).subtype

theorem cupHighestFirstBoundaryEval_vector (q : ℝ) (hq : q≠0) (n : ℕ) (hn : 0<n)
    (l m h c : ℕ) (hm : m≤c) (r : QuantumCupIndex l m c) :
    cupHighestFirstBoundaryEval q n l m h c (quantumCupVector q n l m h c r) =
      if r.val.val=0 then q^(-(h:ℤ)*(m:ℤ)-(m:ℤ)^2+(m:ℤ)) else 0 := by
  change quantumCupMonomial q n (l:ℤ) (h:ℤ) (c:ℤ) r.val.val (m-r.val.val)
    (quantumCupBoundaryPoint n (l:ℤ) (h:ℤ) (c:ℤ) 0 m) = _
  by_cases hr : r.val.val=0
  · rw [hr,Nat.sub_zero,if_pos rfl,
      quantumCupBoundary_diagonal q hq n hn (l:ℤ) (h:ℤ) (c:ℤ) 0 m (by omega) (by omega) (by omega)]
    simp only [Nat.cast_zero,zero_mul,zero_sub]
    congr 1
    ring
  · rw [if_neg hr]
    apply quantumCupBoundary_above_zero q n hn
    have ht:=r.val.isLt
    omega

/-- The first-mixed-highest boundary has a positive rank-transport ratio.
Only cup index zero survives, so there is no term-dependent phase. -/
theorem quantumCupRankReduction_highest_first_boundary (q : ℝ) (hq : 0<q)
    (n : ℕ) (hn : 0<n) (l m h c : ℕ) (hm : m≤c)
    (v : quantumCupSpan q n l m h c) :
    cupHighestFirstBoundaryEval q 1 l m (h+n-1) c (quantumCupRankReduction q hq n hn l m h c v) =
      q^(-((n-1:ℕ):ℤ)*(m:ℤ))*cupHighestFirstBoundaryEval q n l m h c v := by
  have he : (cupHighestFirstBoundaryEval q 1 l m (h+n-1) c).comp
      (quantumCupRankReduction q hq n hn l m h c).toLinearMap =
      q^(-((n-1:ℕ):ℤ)*(m:ℤ)) • cupHighestFirstBoundaryEval q n l m h c := by
    apply (quantumCupBasis q hq n hn l m h c).ext
    intro r
    simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,quantumCupBasis_apply,
      quantumCupRankReduction_vector,map_smul,smul_eq_mul,LinearMap.smul_apply]
    rw [cupHighestFirstBoundaryEval_vector q (ne_of_gt hq) 1 (by omega) l m (h+n-1) c hm,
      cupHighestFirstBoundaryEval_vector q (ne_of_gt hq) n hn l m h c hm]
    by_cases hr : r.val.val=0
    · rw [if_pos hr,if_pos hr]
      simp only [quantumCupRankGauge,hr,Nat.mul_zero,pow_zero,one_mul]
      rw [← zpow_add₀ (ne_of_gt hq)]
      congr 1
      have hcast : ((h+n-1:ℕ):ℤ)=(h:ℤ)+((n-1:ℕ):ℤ) := by omega
      rw [hcast]
      ring
    · rw [if_neg hr,if_neg hr,mul_zero,mul_zero]
  exact DFunLike.congr_fun he v

end AMSPhysical
#print axioms AMSPhysical.quantumCupRankReduction_highest_first_boundary
