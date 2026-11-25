import FiniteWeightedHilbert

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
noncomputable section
namespace AMSPhysical
open Module
variable {ι κ V : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [AddCommGroup V] [Module ℝ V]

theorem finiteWeightedPair_sum_basis (b : Basis ι ℝ V) (w : ι → ℝ)
    (e : κ → ι) (he : Function.Injective e) (c : κ → ℝ) :
    finiteWeightedPair w b.equivFun.toLinearMap (∑ k,c k • b (e k)) (∑ k,c k • b (e k))=
      ∑ k,w (e k)*(c k)^2 := by
  change finiteWeightedBilin w b.equivFun.toLinearMap (∑ k,c k • b (e k)) (∑ k,c k • b (e k))=_
  simp only [map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mul_sum]
  rw [Finset.sum_eq_single k]
  · change c k*(c k*finiteWeightedPair w b.equivFun.toLinearMap (b (e k)) (b (e k)))=_
    rw [finiteWeightedPair_basis,if_pos rfl]
    ring
  · intro j hj hjk
    change c k*(c j*finiteWeightedPair w b.equivFun.toLinearMap (b (e j)) (b (e k)))=0
    rw [finiteWeightedPair_basis,if_neg (fun h => hjk (he h)),mul_zero,mul_zero]
  · intro h
    exact (h (Finset.mem_univ k)).elim

end AMSPhysical

#print axioms AMSPhysical.finiteWeightedPair_sum_basis
