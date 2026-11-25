import StandardPairTransfer
import StandardClebschFirstCoordinate

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem quantumTensorBilin_basis_right_coordinate (q:ℝ) (l m:ℕ)
    (v:finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m) (i:Fin (l+1)) (j:Fin (m+1)) :
    quantumTensorBilin q l m v (standardWeightBasis l i ⊗ₜ[ℝ] standardWeightBasis m j)=
      (quantumWeight q l i.val*quantumWeight q m j.val)*
        ((standardWeightBasis (K:=ℝ) l).tensorProduct (standardWeightBasis (K:=ℝ) m)).repr v (i,j) := by
  rw [← Module.Basis.tensorProduct_apply (standardWeightBasis (K:=ℝ) l) (standardWeightBasis (K:=ℝ) m) i j]
  change finiteWeightedPair (fun p:Fin (l+1) × Fin (m+1)=>quantumWeight q l p.1.val*quantumWeight q m p.2.val)
    ((standardWeightBasis (K:=ℝ) l).tensorProduct (standardWeightBasis (K:=ℝ) m)).equivFun.toLinearMap v
      ((standardWeightBasis (K:=ℝ) l).tensorProduct (standardWeightBasis (K:=ℝ) m) (i,j))=_
  rw [finiteWeightedPair_basis_right]
  rfl

/-- Exact single-channel first-coordinate kernel, obtained from actual
Clebsch adjunction and weight support, before any factorial evaluation. -/
theorem standardPairTransfer_first_coordinate (q:ℝ) (hq:0<q) (hq1:q≠1)
    (l m:ℕ) (r:Fin (min l m+1)) (l' m':ℕ) (s:Fin (min l' m'+1))
    (L:ℕ) (hr:coupledLabel l m r=L) (hs:coupledLabel l' m' s=L)
    (k:Fin (L+1)) (z:Fin (m+1)) (z':Fin (m'+1)) (hz:z.val=r.val+k.val) :
    ((standardWeightBasis (K:=ℝ) l').tensorProduct (standardWeightBasis (K:=ℝ) m')).repr
      (standardPairTransfer q hq hq1 l m r l' m' s L hr hs
        (standardWeightBasis l 0 ⊗ₜ[ℝ] standardWeightBasis m z)) (0,z')=
      (quantumWeight q m z.val*
        ((standardWeightBasis (K:=ℝ) l).tensorProduct (standardWeightBasis (K:=ℝ) m)).repr
          (standardClebschAtLabel q hq hq1 l m r L hr (standardWeightBasis L k)) (0,z)/quantumWeight q L k.val)*
        ((standardWeightBasis (K:=ℝ) l').tensorProduct (standardWeightBasis (K:=ℝ) m')).repr
          (standardClebschAtLabel q hq hq1 l' m' s L hs (standardWeightBasis L k)) (0,z') := by
  classical
  rw [standardPairTransfer_expansion,map_sum]
  simp only [Finsupp.finset_sum_apply,map_smul,Finsupp.smul_apply,smul_eq_mul,Fin.val_zero,
    quantumTensorBilin_basis_right_coordinate,quantumWeight_zero q hq,one_mul]
  rw [Finset.sum_eq_single k]
  · intro j hj hjk
    rw [standardClebschAtLabel_first_mismatch q hq hq1 l m r L hr j z (by
      intro he
      apply hjk
      apply Fin.ext
      omega),mul_zero,zero_div,zero_mul]
  · simp

/-- Every physical source boundary below its contraction index is killed
by the entire selected pair map, not just by one target coefficient. -/
theorem standardPairTransfer_first_input_below (q:ℝ) (hq:0<q) (hq1:q≠1)
    (l m:ℕ) (r:Fin (min l m+1)) (l' m':ℕ) (s:Fin (min l' m'+1))
    (L:ℕ) (hr:coupledLabel l m r=L) (hs:coupledLabel l' m' s=L)
    (z:Fin (m+1)) (hz:z.val<r.val) :
    standardPairTransfer q hq hq1 l m r l' m' s L hr hs
      (standardWeightBasis l 0 ⊗ₜ[ℝ] standardWeightBasis m z)=0 := by
  rw [standardPairTransfer_expansion]
  apply Finset.sum_eq_zero
  intro k hk
  rw [quantumTensorBilin_basis_right_coordinate]
  simp only [Fin.val_zero,quantumWeight_zero q hq,one_mul]
  rw [standardClebschAtLabel_first_below q hq hq1 l m r L hr k z hz,mul_zero,zero_div,zero_smul]

end AMSPhysical
#print axioms AMSPhysical.standardPairTransfer_first_coordinate
#print axioms AMSPhysical.standardPairTransfer_first_input_below
