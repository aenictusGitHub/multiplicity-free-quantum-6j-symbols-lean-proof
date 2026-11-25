import TensorBasisDiagonal

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
open Module
open scoped TensorProduct
variable {K V W I J T : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] [Fintype T]

theorem tensor_sum_right_coefficient (b : Basis I K V) (d : Basis J K W)
    (g : T → J) (hg : Function.Injective g) (c : T → K) (v : T → V) (x : I) (t : T) :
    (b.tensorProduct d).repr (∑ u,c u • (v u ⊗ₜ[K] d (g u))) (x,g t)=c t*b.repr (v t) x := by
  classical
  simp [map_sum,Finsupp.sum_apply,Finsupp.smul_apply,Module.Basis.tensorProduct_repr_tmul_apply,
    Module.Basis.repr_self,Finsupp.single_apply,hg.eq_iff,eq_comm]

theorem tensor_sum_left_coefficient (b : Basis I K V) (d : Basis J K W)
    (f : T → I) (hf : Function.Injective f) (c : T → K) (w : T → W) (t : T) (y : J) :
    (b.tensorProduct d).repr (∑ u,c u • (b (f u) ⊗ₜ[K] w u)) (f t,y)=c t*d.repr (w t) y := by
  classical
  simp [map_sum,Finsupp.sum_apply,Finsupp.smul_apply,Module.Basis.tensorProduct_repr_tmul_apply,
    Module.Basis.repr_self,Finsupp.single_apply,hf.eq_iff,eq_comm]

end AMSPhysical
#print axioms AMSPhysical.tensor_sum_left_coefficient
