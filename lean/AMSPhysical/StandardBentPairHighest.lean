import StandardPairFirstCoordinate
import TensorAssociatorCoordinate
import QuantumTypeIILeftBoundary

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

/-- Actual standard pair-isometry bending, allowing different source and
target determinant backgrounds. No overlap candidate defines this vector. -/
def standardBentPairHighest (q:ℝ) (hq:0<q) (hq1:q≠1) (d c:ℕ) (r:Fin (min d c+1))
    (a b:ℕ) (s:Fin (min a b+1)) (L:ℕ)
    (hr:coupledLabel d c r=L) (hs:coupledLabel a b s=L) :
    finiteWeightSpace (K:=ℝ) a ⊗[ℝ] (finiteWeightSpace (K:=ℝ) b ⊗[ℝ] finiteWeightSpace (K:=ℝ) c) :=
  (TensorProduct.assoc ℝ _ _ _)
    (bendRight (standardPairTransfer q hq hq1 d c r a b s L hr hs)
      (typeIIStandardBoundaryCup q c) (standardWeightBasis d 0))

theorem standardBentPairHighest_coordinate (q:ℝ) (hq:0<q) (hq1:q≠1) (d c:ℕ) (r:Fin (min d c+1))
    (a b:ℕ) (s:Fin (min a b+1)) (L:ℕ)
    (hr:coupledLabel d c r=L) (hs:coupledLabel a b s=L)
    (k:Fin (L+1)) (z:Fin (c+1)) (j:Fin (b+1)) (hz:z.val=r.val+k.val) :
    ((standardWeightBasis (K:=ℝ) a).tensorProduct
      ((standardWeightBasis (K:=ℝ) b).tensorProduct (standardWeightBasis (K:=ℝ) c))).repr
      (standardBentPairHighest q hq hq1 d c r a b s L hr hs) (0,(j,z))=
      ((-1:ℝ)^(z.val:ℤ)*
        ((standardWeightBasis (K:=ℝ) d).tensorProduct (standardWeightBasis (K:=ℝ) c)).repr
          (standardClebschAtLabel q hq hq1 d c r L hr (standardWeightBasis L k)) (0,z)*
        ((standardWeightBasis (K:=ℝ) a).tensorProduct (standardWeightBasis (K:=ℝ) b)).repr
          (standardClebschAtLabel q hq hq1 a b s L hs (standardWeightBasis L k)) (0,j))/quantumWeight q L k.val := by
  unfold standardBentPairHighest typeIIStandardBoundaryCup
  rw [tensor_assoc_coordinate,bendRight_diagonal_coordinate]
  rw [standardPairTransfer_first_coordinate q hq hq1 d c r a b s L hr hs k z j hz]
  field_simp [ne_of_gt (quantumWeight_pos q hq c z.val),ne_of_gt (quantumWeight_pos q hq L k.val)]

/-- Exact support of the entire independently bent vector on its last leg. -/
theorem standardBentPairHighest_below (q:ℝ) (hq:0<q) (hq1:q≠1) (d c:ℕ) (r:Fin (min d c+1))
    (a b:ℕ) (s:Fin (min a b+1)) (L:ℕ)
    (hr:coupledLabel d c r=L) (hs:coupledLabel a b s=L)
    (i:Fin (a+1)) (j:Fin (b+1)) (z:Fin (c+1)) (hz:z.val<r.val) :
    ((standardWeightBasis (K:=ℝ) a).tensorProduct
      ((standardWeightBasis (K:=ℝ) b).tensorProduct (standardWeightBasis (K:=ℝ) c))).repr
      (standardBentPairHighest q hq hq1 d c r a b s L hr hs) (i,(j,z))=0 := by
  unfold standardBentPairHighest typeIIStandardBoundaryCup
  rw [tensor_assoc_coordinate,bendRight_diagonal_coordinate,
    standardPairTransfer_first_input_below q hq hq1 d c r a b s L hr hs z hz,map_zero,Finsupp.zero_apply,mul_zero]

theorem standardBentPairHighest_leading (q:ℝ) (hq:0<q) (hq1:q≠1) (d c:ℕ) (r:Fin (min d c+1))
    (a b:ℕ) (s:Fin (min a b+1)) (L:ℕ)
    (hr:coupledLabel d c r=L) (hs:coupledLabel a b s=L)
    (z:Fin (c+1)) (j:Fin (b+1)) (hz:z.val=r.val) (hj:j.val=s.val) :
    ((standardWeightBasis (K:=ℝ) a).tensorProduct
      ((standardWeightBasis (K:=ℝ) b).tensorProduct (standardWeightBasis (K:=ℝ) c))).repr
      (standardBentPairHighest q hq hq1 d c r a b s L hr hs) (0,(j,z))=
      (-1:ℝ)^(r.val:ℤ)/
        (Real.sqrt (quantumHighestNorm q d c r)*Real.sqrt (quantumHighestNorm q a b s)) := by
  rw [standardBentPairHighest_coordinate q hq hq1 d c r a b s L hr hs 0 z j (by simpa using hz),
    standardClebschAtLabel_first_highest q hq hq1 d c r L hr z hz,
    standardClebschAtLabel_first_highest q hq hq1 a b s L hs j hj]
  simp only [Fin.val_zero,quantumWeight_zero q hq,hz,div_one]
  ring

end AMSPhysical
#print axioms AMSPhysical.standardBentPairHighest_below
#print axioms AMSPhysical.standardBentPairHighest_leading
