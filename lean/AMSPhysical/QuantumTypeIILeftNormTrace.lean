import QuantumTypeIILeftTreeMetric
import QuantumTypeIIHighestBoundary
import QuantumPositivePivot
import FiniteBendingWeightedSum
import WeightedProjectionTrace
import QuantumReverseLoop
import QuantumMixedIrrepDimension

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 500000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem occupationOpposite_compact_ratio (q:ℝ) (hq:0<q) (n L:ℕ)
    (x:occupationWeights (Fin (n+1)) L) :
    occupationOppositeWeight q n L x/occupationCompactWeight q n L x=
      q^(latticePairing (-typeAInversePivotalWeight n) x.val) := by
  rw [latticePairing_neg_left_typeA,zpow_neg,← occupationCompact_opposite_ratio q hq,inv_div]

/-- Actual raw Type-II tree norm is a positive-pivotal trace ratio.
Both sides refer to independently constructed physical maps and metrics. -/
theorem physicalTypeIILeftHighestNormSq_trace (q:ℝ) (hq:0<q) (hq1:q≠1)
    (n:ℕ) (hn:0<n) (a b c d:ℕ) (hbal:a+b=c+d) (r:TypeIICommonIndex a b c d) :
    physicalTypeIILeftHighestNormSq q hq hq1 n hn a b c d hbal r*symmetricQuantumDimension q n d=
      LinearMap.trace ℝ (typeIILeftSource q hq hq1 n hn a b c d hbal r).channel
        ((typeIILeftSource q hq hq1 n hn a b c d hbal r).channelAction (typeAPositivePivot q (ne_of_gt hq) n)) := by
  let V:=quantumOccupationSpace ℝ (Fin (n+1)) d ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) c
  let W:=quantumOccupationSpace ℝ (Fin (n+1)) a ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) b
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  letI : AddCommGroup W := inferInstance
  letI : Module ℝ W := inferInstance
  letI : Module.Finite ℝ V:=Module.Finite.of_basis
    ((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) d).tensorProduct (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) c))
  letI : Module.Finite ℝ W:=Module.Finite.of_basis
    ((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) a).tensorProduct (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) b))
  let bd:=quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) d
  let bc:=quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) c
  let bt:Module.Basis (occupationWeights (Fin (n+1)) a × occupationWeights (Fin (n+1)) b) ℝ W:=
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) a).tensorProduct (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) b)
  let X:=typeIILeftSource q hq hq1 n hn a b c d hbal r
  let Y:=typeIILeftTarget q hq hq1 n hn a b c d r
  let e (L:ℕ) (x:occupationWeights (Fin (n+1)) L):ℝ:=q^(latticePairing (-typeAInversePivotalWeight n) x.val)
  let F:V →ₗ[ℝ] W:=physicalTypeIILeftPairMap q hq hq1 n hn a b c d hbal r
  let N:=physicalTypeIILeftHighestNormSq q hq hq1 n hn a b c d hbal r
  have hCup (x:occupationWeights (Fin (n+1)) c) :
      (occupationDualSign n c x/occupationCompactWeight q n c x)*
        (occupationDualSign n c x/occupationCompactWeight q n c x)*occupationOppositeWeight q n c x=
      e c x/occupationCompactWeight q n c x := by
    rw [div_mul_div_comm,occupationDualSign_square]
    dsimp only [e]
    rw [← occupationOpposite_compact_ratio q hq]
    ring
  have hN (x:occupationWeights (Fin (n+1)) d) :
      tensorWeightedBilin bt bc (fun xy=>occupationCompactWeight q n a xy.1*occupationCompactWeight q n b xy.2)
        (occupationOppositeWeight q n c)
        (bendRight F (diagonalCoevaluation bc (fun y=>occupationDualSign n c y/occupationCompactWeight q n c y)) (bd x))
        (bendRight F (diagonalCoevaluation bc (fun y=>occupationDualSign n c y/occupationCompactWeight q n c y)) (bd x))=
      N*occupationCompactWeight q n d x := by
    have he:=physicalTypeIILeftTreeMap_metric q hq hq1 n hn a b c d hbal r (bd x) (bd x)
    rw [physicalTypeIILeftTreeMap_eq_bend] at he
    simp only [LinearMap.comp_apply,LinearEquiv.coe_coe] at he
    rw [physicalTypeIITripleBilin_assoc,symmetricCoevaluation_diagonal] at he
    change _=N*finiteWeightedPair (occupationCompactWeight q n d) bd.equivFun.toLinearMap (bd x) (bd x) at he
    rwa [finiteWeightedPair_basis,if_pos rfl] at he
  have hs:=bendRight_metric_weighted_sum
    (X:=quantumOccupationSpace ℝ (Fin (n+1)) d)
    (V:=quantumOccupationSpace ℝ (Fin (n+1)) c) (W:=W) bd bc bt
    (occupationCompactWeight q n d) (occupationCompactWeight q n c)
    (fun y=>occupationDualSign n c y/occupationCompactWeight q n c y) (occupationOppositeWeight q n c)
    (fun xy=>occupationCompactWeight q n a xy.1*occupationCompactWeight q n b xy.2)
    (e d) (e c) N
    (fun x=>ne_of_gt (occupationCompactWeight_pos q hq n d x))
    (fun x=>ne_of_gt (occupationCompactWeight_pos q hq n c x)) hCup F hN
  have heSum:(∑ x,e d x)=symmetricQuantumDimension q n d := by
    unfold symmetricQuantumDimension
    rw [← typeAOpposite_pivotal_dimension q hq (qInteger_denominator_ne_zero q hq hq1) n d,
      typeAOpposite_inversePivot_representation,finiteOccupationCartan_trace]
  rw [heSum] at hs
  have hB (p:occupationWeights (Fin (n+1)) d × occupationWeights (Fin (n+1)) c) (v:V) :
      X.pairing ((bd.tensorProduct bc) p) v=
        (occupationCompactWeight q n d p.1*occupationCompactWeight q n c p.2)*(bd.tensorProduct bc).repr v p := by
    change finiteWeightedPair (fun xy=>occupationCompactWeight q n d xy.1*occupationCompactWeight q n c xy.2)
      (bd.tensorProduct bc).equivFun.toLinearMap ((bd.tensorProduct bc) p) v=_
    rw [finiteWeightedPair_symm,finiteWeightedPair_basis_right]
    rfl
  have ht:=CompactHighestRealization.channelTransfer_weighted_trace (V:=V) (W:=W) (ne_of_gt hq) X Y
    (bd.tensorProduct bc) (fun xy=>occupationCompactWeight q n d xy.1*occupationCompactWeight q n c xy.2)
    (fun p=>mul_ne_zero (ne_of_gt (occupationCompactWeight_pos q hq n d p.1))
      (ne_of_gt (occupationCompactWeight_pos q hq n c p.2))) hB
    (typeAPositivePivot q (ne_of_gt hq) n) (fun p=>e d p.1*e c p.2)
    (fun p=>by
      change typeASymmetricTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n d c
        (typeAPositivePivot q (ne_of_gt hq) n) ((bd.tensorProduct bc) p)=_
      rw [typeASymmetricTensor_positivePivot_basis,zpow_add₀ (ne_of_gt hq)])
  have hF:X.channelTransfer (ne_of_gt hq) Y=F:=rfl
  have hYP:Y.pairing=symmetricTensorBilin q n a b:=rfl
  rw [hF,hYP] at ht
  rw [hs]
  calc
    _=∑ p:occupationWeights (Fin (n+1)) d × occupationWeights (Fin (n+1)) c,
        e d p.1*e c p.2/(occupationCompactWeight q n d p.1*occupationCompactWeight q n c p.2)*
          symmetricTensorBilin q n a b (F ((bd.tensorProduct bc) p)) (F ((bd.tensorProduct bc) p)) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Module.Basis.tensorProduct_apply']
      rfl
    _=_ := ht

end AMSPhysical
#print axioms AMSPhysical.physicalTypeIILeftHighestNormSq_trace
