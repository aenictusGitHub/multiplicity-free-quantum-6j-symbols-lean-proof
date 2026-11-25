import QuantumClebschSingleSum
import QuantumTripleMetric

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem finiteTensorForget_coefficient (l m:ℕ)
    (v:finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m) (i:Fin (l+1)) (j:Fin (m+1)) :
    tensorCoefficient (i.val:ℤ) (j.val:ℤ) (finiteTensorForget l m v)=
      ((standardWeightBasis (K:=ℝ) l).tensorProduct (standardWeightBasis (K:=ℝ) m)).repr v (i,j) := by
  classical
  have he:(tensorCoefficient (K:=ℝ) (i.val:ℤ) (j.val:ℤ)).comp (finiteTensorForget l m)=
      (Finsupp.lapply (i,j)).comp
        ((standardWeightBasis (K:=ℝ) l).tensorProduct (standardWeightBasis (K:=ℝ) m)).repr.toLinearMap := by
    apply ((standardWeightBasis (K:=ℝ) l).tensorProduct (standardWeightBasis (K:=ℝ) m)).ext
    rintro ⟨u,w⟩
    simp only [LinearMap.comp_apply,Module.Basis.tensorProduct_apply',finiteTensorForget,TensorProduct.map_tmul,
      standardWeightBasis_apply,Submodule.subtype_apply]
    change tensorCoefficient (K:=ℝ) (i.val:ℤ) (j.val:ℤ) (tensorWeightBasis (u.val:ℤ) (w.val:ℤ))=_
    rw [tensorCoefficient_basis]
    change _=(((standardWeightBasis (K:=ℝ) l).tensorProduct (standardWeightBasis (K:=ℝ) m)).repr
      (standardWeightVector l u ⊗ₜ[ℝ] standardWeightVector m w)) (i,j)
    rw [← standardWeightBasis_apply,← standardWeightBasis_apply,
      ← Module.Basis.tensorProduct_apply (standardWeightBasis (K:=ℝ) l) (standardWeightBasis (K:=ℝ) m) u w,
      Module.Basis.repr_self]
    simp only [Finsupp.single_apply,Prod.mk.injEq,Int.natCast_inj,← Fin.ext_iff]
    by_cases hu:u=i <;> by_cases hw:w=j <;> simp [hu,hw]
  exact DFunLike.congr_fun he v

theorem standardClebschCoefficient_eq_repr (q:ℝ) (hq:0<q) (hq1:q≠1) (l m:ℕ)
    (r:Fin (min l m+1)) (k:Fin (coupledLabel l m r+1)) (i:Fin (l+1)) (j:Fin (m+1)) :
    standardClebschCoefficient q hq hq1 l m r k (i.val:ℤ) (j.val:ℤ)=
      ((standardWeightBasis (K:=ℝ) l).tensorProduct (standardWeightBasis (K:=ℝ) m)).repr
        (unitaryQuantumClebschMap q hq hq1 l m r (standardWeightBasis (coupledLabel l m r) k)) (i,j) :=
  finiteTensorForget_coefficient l m _ i j

end AMSPhysical
#print axioms AMSPhysical.standardClebschCoefficient_eq_repr
