import StandardBentPairHighest
import StandardPairFirstInput
import StandardBentCoefficientCancellation
import FiniteSumSupportShift

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

/-- Complete vector expansion of the independently bent standard pair map.
The source adjunction coefficient cancels the physical cup metric exactly. -/
theorem standardBentPairHighest_expansion (q:ℝ) (hq:0<q) (hq1:q≠1) (d c:ℕ)
    (r:Fin (min d c+1)) (a b:ℕ) (s:Fin (min a b+1)) (L:ℕ)
    (hr:coupledLabel d c r=L) (hs:coupledLabel a b s=L):
    standardBentPairHighest q hq hq1 d c r a b s L hr hs=
      ∑ t:Fin (c-r.val+1),
        (((-1:ℝ)^(r.val:ℤ))/(Real.sqrt (quantumHighestNorm q d c r))*
          couplingCoefficient q (c:ℤ) (c-r.val) t.val) •
        (TensorProduct.assoc ℝ _ _ _)
          (standardClebschAtLabel q hq hq1 a b s L hs
            (standardWeightBasis L ⟨t.val,by
              have ht:=t.isLt
              have hrd:=channel_left_bound d c r
              have hrc:=channel_right_bound d c r
              unfold coupledLabel at hr
              omega⟩) ⊗ₜ[ℝ]
            standardWeightBasis c ⟨r.val+t.val,by have ht:=t.isLt;have hrc:=channel_right_bound d c r;omega⟩) := by
  have hrd:=channel_left_bound d c r
  have hrc:=channel_right_bound d c r
  unfold standardBentPairHighest typeIIStandardBoundaryCup
  rw [bendRight_diagonal]
  have hz (k:Fin (c+1)) (hk:k.val<r.val):
      ((-1:ℝ)^(k.val:ℤ)/quantumWeight q c k.val) •
        (standardPairTransfer q hq hq1 d c r a b s L hr hs
          (standardWeightBasis d 0 ⊗ₜ[ℝ] standardWeightBasis (K:=ℝ) c k) ⊗ₜ[ℝ] standardWeightBasis (K:=ℝ) c k)=0:=by
    rw [standardPairTransfer_first_input_below q hq hq1 d c r a b s L hr hs k hk,TensorProduct.zero_tmul,smul_zero]
  rw [fin_sum_zero_below_shift r.val c hrc _ hz,map_sum]
  apply Finset.sum_congr rfl
  intro t ht
  let k:Fin (L+1):=⟨t.val,by have hti:=t.isLt;unfold coupledLabel at hr;omega⟩
  let z:Fin (c+1):=⟨r.val+t.val,by have hti:=t.isLt;omega⟩
  simp only [map_smul]
  rw [standardPairTransfer_first_input q hq hq1 d c r a b s L hr hs k z (by rfl)]
  simp only [← TensorProduct.smul_tmul',map_smul,smul_smul]
  congr 1
  have he:=standardBent_source_coefficient q hq hq1 d c r L hr k z (by rfl)
  calc
    _=((-1:ℝ)^(z.val:ℤ))*
      ((standardWeightBasis (K:=ℝ) d).tensorProduct (standardWeightBasis (K:=ℝ) c)).repr
        (standardClebschAtLabel q hq hq1 d c r L hr (standardWeightBasis L k)) (0,z)/quantumWeight q L k.val:=by
      dsimp only [z]
      field_simp [ne_of_gt (quantumWeight_pos q hq c (r.val+t.val)),
        ne_of_gt (quantumWeight_pos q hq L k.val)]
    _=_:=he

end AMSPhysical
#print axioms AMSPhysical.standardBentPairHighest_expansion
