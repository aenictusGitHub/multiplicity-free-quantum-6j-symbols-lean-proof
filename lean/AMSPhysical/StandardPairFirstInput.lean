import StandardPairFirstCoordinate

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

/-- The whole standard pair output, not merely one target coefficient,
is selected by the unique source root weight. -/
theorem standardPairTransfer_first_input (q:ℝ) (hq:0<q) (hq1:q≠1)
    (l m:ℕ) (r:Fin (min l m+1)) (l' m':ℕ) (s:Fin (min l' m'+1))
    (L:ℕ) (hr:coupledLabel l m r=L) (hs:coupledLabel l' m' s=L)
    (k:Fin (L+1)) (z:Fin (m+1)) (hz:z.val=r.val+k.val) :
    standardPairTransfer q hq hq1 l m r l' m' s L hr hs
      (standardWeightBasis l 0 ⊗ₜ[ℝ] standardWeightBasis m z)=
      (quantumWeight q m z.val*
        ((standardWeightBasis (K:=ℝ) l).tensorProduct (standardWeightBasis (K:=ℝ) m)).repr
          (standardClebschAtLabel q hq hq1 l m r L hr (standardWeightBasis L k)) (0,z)/quantumWeight q L k.val) •
        standardClebschAtLabel q hq hq1 l' m' s L hs (standardWeightBasis L k) := by
  classical
  rw [standardPairTransfer_expansion]
  simp only [quantumTensorBilin_basis_right_coordinate,Fin.val_zero,quantumWeight_zero q hq,one_mul]
  apply Finset.sum_eq_single k
  · intro j hj hjk
    rw [standardClebschAtLabel_first_mismatch q hq hq1 l m r L hr j z (by
      intro he
      apply hjk
      apply Fin.ext
      omega),mul_zero,zero_div,zero_smul]
  · simp

end AMSPhysical
#print axioms AMSPhysical.standardPairTransfer_first_input
