import QuantumTypeIICreationBoundary

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

/-- Literal first-leg highest coordinate, extended by zero outside the finite
second and third weight ranges. -/
def standardBoundaryCoordinate (a b c j k:ℕ):
    (finiteWeightSpace (K:=ℝ) a ⊗[ℝ]
      (finiteWeightSpace (K:=ℝ) b ⊗[ℝ] finiteWeightSpace (K:=ℝ) c)) →ₗ[ℝ] ℝ :=
  if hj:j<b+1 then if hk:k<c+1 then
    (Finsupp.lapply (0,(⟨j,hj⟩,⟨k,hk⟩))).comp
      ((standardWeightBasis (K:=ℝ) a).tensorProduct
        ((standardWeightBasis (K:=ℝ) b).tensorProduct (standardWeightBasis (K:=ℝ) c))).repr.toLinearMap
    else 0 else 0

theorem standardBoundaryCoordinate_basis (a b c j k:ℕ)
    (i:Fin (a+1)) (u:Fin (b+1)) (v:Fin (c+1)):
    standardBoundaryCoordinate a b c j k
      (standardWeightBasis a i ⊗ₜ[ℝ] (standardWeightBasis b u ⊗ₜ[ℝ] standardWeightBasis c v))=
      if i.val=0 ∧ u.val=j ∧ v.val=k then 1 else 0 := by
  classical
  unfold standardBoundaryCoordinate
  by_cases hj:j<b+1
  · rw [dif_pos hj]
    by_cases hk:k<c+1
    · rw [dif_pos hk]
      change (((standardWeightBasis (K:=ℝ) a).tensorProduct
          ((standardWeightBasis (K:=ℝ) b).tensorProduct (standardWeightBasis (K:=ℝ) c))).repr
          (standardWeightBasis a i ⊗ₜ[ℝ] (standardWeightBasis b u ⊗ₜ[ℝ] standardWeightBasis c v)))
          (0,(⟨j,hj⟩,⟨k,hk⟩))=_
      rw [← Module.Basis.tensorProduct_apply (standardWeightBasis (K:=ℝ) b) (standardWeightBasis (K:=ℝ) c) u v,
        ← Module.Basis.tensorProduct_apply (standardWeightBasis (K:=ℝ) a)
          ((standardWeightBasis (K:=ℝ) b).tensorProduct (standardWeightBasis (K:=ℝ) c)) i (u,v),
        Module.Basis.repr_self]
      simp only [Finsupp.single_apply,Prod.mk.injEq,Fin.ext_iff,Fin.val_zero,Fin.val_mk]
    · rw [dif_neg hk]
      simp only [LinearMap.zero_apply]
      have hv:=v.isLt
      rw [if_neg (by rintro ⟨_,_,he⟩;omega)]
  · rw [dif_neg hj]
    simp only [LinearMap.zero_apply]
    have hu:=u.isLt
    rw [if_neg (by rintro ⟨_,he,_⟩;omega)]

/-- Exact two-term creation recurrence on every vector, including endpoints.
The second coordinate is k+h, so its finite difference has the determinant
background coefficient q^(-h). -/
theorem standardBoundaryCoordinate_creation (q:ℝ) (a b c h k:ℕ)
    (w:finiteWeightSpace (K:=ℝ) a ⊗[ℝ]
      (finiteWeightSpace (K:=ℝ) b ⊗[ℝ] finiteWeightSpace (K:=ℝ) c)):
    standardBoundaryCoordinate a (b+1) (c+1) (k+h) k (typeIIStandardRightCreation q a b c w)=
      q^(-((b-(k+h):ℕ):ℤ)-((c-k:ℕ):ℤ))*standardBoundaryCoordinate a b c (k+h) k w-
        q^(-1-(b:ℤ)-(c:ℤ))*
          (if k=0 then 0 else standardBoundaryCoordinate a b c (k+h-1) (k-1) w) := by
  classical
  have he:(standardBoundaryCoordinate a (b+1) (c+1) (k+h) k).comp (typeIIStandardRightCreation q a b c)=
      q^(-((b-(k+h):ℕ):ℤ)-((c-k:ℕ):ℤ)) • standardBoundaryCoordinate a b c (k+h) k-
        q^(-1-(b:ℤ)-(c:ℤ)) • (if k=0 then 0 else standardBoundaryCoordinate a b c (k+h-1) (k-1)):=by
    apply ((standardWeightBasis (K:=ℝ) a).tensorProduct
      ((standardWeightBasis (K:=ℝ) b).tensorProduct (standardWeightBasis (K:=ℝ) c))).ext
    rintro ⟨i,u,v⟩
    by_cases hk:k=0
    ·
      simp only [hk,Module.Basis.tensorProduct_apply',LinearMap.comp_apply,typeIIStandardRightCreation,
        TensorProduct.map_tmul,LinearMap.id_apply,mixedTwoVertexCompressedCreation_basis,
        TensorProduct.tmul_add,TensorProduct.tmul_smul,map_add,map_smul,smul_eq_mul,
        LinearMap.sub_apply,LinearMap.smul_apply,standardBoundaryCoordinate_basis,
        Fin.coe_castSucc,Fin.val_succ,ite_apply,LinearMap.zero_apply,if_true,if_false]
      split_ifs <;> simp_all [standardBoundaryCoordinate_basis]
    ·
      simp only [hk,Module.Basis.tensorProduct_apply',LinearMap.comp_apply,typeIIStandardRightCreation,
        TensorProduct.map_tmul,LinearMap.id_apply,mixedTwoVertexCompressedCreation_basis,
        TensorProduct.tmul_add,TensorProduct.tmul_smul,map_add,map_smul,smul_eq_mul,
        LinearMap.sub_apply,LinearMap.smul_apply,standardBoundaryCoordinate_basis,
        Fin.coe_castSucc,Fin.val_succ,ite_apply,LinearMap.zero_apply,if_true,if_false]
      have hp:(i.val=0 ∧ u.val=k+h-1 ∧ v.val=k-1) ↔
          (i.val=0 ∧ u.val+1=k+h ∧ v.val+1=k):=by omega
      simp only [hp]
      by_cases hX:i.val=0 ∧ u.val=k+h ∧ v.val=k
      · by_cases hY:i.val=0 ∧ u.val+1=k+h ∧ v.val+1=k
        · omega
        · rw [if_pos hX,if_neg hY]
          simp only [mul_one,mul_zero,add_zero,sub_zero]
          rw [hX.2.1,hX.2.2]
      · by_cases hY:i.val=0 ∧ u.val+1=k+h ∧ v.val+1=k
        · rw [if_neg hX,if_pos hY]
          simp only [mul_one,mul_zero,zero_add,zero_sub]
        · rw [if_neg hX,if_neg hY]
          simp only [mul_zero,add_zero,sub_zero]
  by_cases hk:k=0 <;>
    simpa only [hk,LinearMap.comp_apply,LinearMap.sub_apply,LinearMap.smul_apply,smul_eq_mul,
      ite_apply,LinearMap.zero_apply,mul_zero,sub_zero] using DFunLike.congr_fun he w

end AMSPhysical
#print axioms AMSPhysical.standardBoundaryCoordinate_creation
