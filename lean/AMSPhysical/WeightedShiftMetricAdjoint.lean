import InjectedBasisSynthesis
import FiniteWeightedDuality

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
variable {I J S X V W : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype S] [AddCommGroup X] [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- Independent coefficient formulas for two finite maps determine their
physical adjunction from local weighted-shift balance. -/
theorem weightedShift_metric_adjoint (b : Module.Basis I ℝ V) (c : Module.Basis J ℝ W)
    (e : I → X) (f : J → X) (he : Function.Injective e) (hf : Function.Injective f)
    (w : I → ℝ) (z : J → ℝ) (R : V →ₗ[ℝ] W) (L : W →ₗ[ℝ] V)
    (s : S → X) (φ ψ : S → X → ℝ) (a : ℝ)
    (hR : ∀ i,injectedBasisCoefficients c f (R (b i))=∑ k : S,Finsupp.single (e i+s k) (φ k (e i)))
    (hL : ∀ j,injectedBasisCoefficients b e (L (c j))=∑ k : S,Finsupp.single (f j-s k) (ψ k (f j)))
    (hbal : ∀ i j k,e i+s k=f j → φ k (e i)*z j=a*ψ k (f j)*w i)
    (v : V) (u : W) :
    finiteWeightedBilin z c.equivFun.toLinearMap (R v) u=
      finiteWeightedBilin w b.equivFun.toLinearMap v (a • L u) := by
  classical
  have hMaps : (finiteWeightedBilin z c.equivFun.toLinearMap).comp R=
      (finiteWeightedBilin w b.equivFun.toLinearMap).compl₂ (a • L) := by
    apply b.ext
    intro i
    apply c.ext
    intro j
    change finiteWeightedPair z c.equivFun.toLinearMap (R (b i)) (c j)=
      finiteWeightedPair w b.equivFun.toLinearMap (b i) (a • L (c j))
    rw [finiteWeightedPair_basis_right,finiteWeightedPair_smul_right,
      finiteWeightedPair_symm w _ (b i) (L (c j)),finiteWeightedPair_basis_right]
    have hr:=congrArg (fun p : X →₀ ℝ => p (f j)) (hR i)
    have hl:=congrArg (fun p : X →₀ ℝ => p (e i)) (hL j)
    simp only [injectedBasisCoefficients,Finsupp.lmapDomain_apply,LinearMap.comp_apply,
      Finsupp.mapDomain_apply hf,Finsupp.mapDomain_apply he,Finsupp.finset_sum_apply,Finsupp.single_apply] at hr hl
    change c.repr (R (b i)) j=_ at hr
    change b.repr (L (c j)) i=_ at hl
    simp only [Module.Basis.equivFun_apply]
    rw [hr,hl]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases h : e i+s k=f j
    · have h' : f j-s k=e i := (sub_eq_iff_eq_add).mpr h.symm
      rw [if_pos h,if_pos h']
      linear_combination hbal i j k h
    · have h' : f j-s k≠e i := by intro hh;apply h;exact ((sub_eq_iff_eq_add).mp hh).symm
      simp only [if_neg h,if_neg h',mul_zero,zero_mul]
  exact DFunLike.congr_fun (DFunLike.congr_fun hMaps v) u

end AMSPhysical
