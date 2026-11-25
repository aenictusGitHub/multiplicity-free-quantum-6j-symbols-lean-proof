import QuantumMixedFiniteAnnihilation
import QuantumMixedAnnihilationBalance
import QuantumMixedContraction
import WeightedShiftMetricAdjoint

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem mixedFiniteRawAnnihilation_adjoint (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n l m : ℕ)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
    (u : quantumOccupationSpace ℝ (Fin (n+1)) (l+1) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (m+1)) :
    mixedTensorBilin q n (l+1) (m+1) (mixedFiniteCreation q n l m v) u=
      mixedTensorBilin q n l m v (mixedAnnihilationScale q n l m • mixedFiniteRawAnnihilation q n l m u) := by
  let V := quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m
  let W := quantumOccupationSpace ℝ (Fin (n+1)) (l+1) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (m+1)
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  letI : AddCommGroup W := inferInstance
  letI : Module ℝ W := inferInstance
  apply weightedShift_metric_adjoint (V:=V) (W:=W)
    ((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l).tensorProduct
      (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m))
    ((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) (l+1)).tensorProduct
      (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) (m+1)))
    (occupationPairEmbedding n l m) (occupationPairEmbedding n (l+1) (m+1))
    (occupationPairEmbedding_injective n l m) (occupationPairEmbedding_injective n (l+1) (m+1))
    (fun xy =>occupationCompactWeight q n l xy.1*occupationOppositeWeight q n m xy.2)
    (fun xy =>occupationCompactWeight q n (l+1) xy.1*occupationOppositeWeight q n (m+1) xy.2)
    (mixedFiniteCreation q n l m) (mixedFiniteRawAnnihilation q n l m)
    (mixedCreationShift n) (mixedCreationCoefficient q n) (mixedAnnihilationCoefficient q n)
    (mixedAnnihilationScale q n l m)
  · intro p
    change occupationTensorCoefficients n (l+1) (m+1)
      (mixedFiniteCreation q n l m
        (((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l).tensorProduct
          (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m)) (p.1,p.2)))=_
    rw [Module.Basis.tensorProduct_apply',occupationTensorCoefficients_creation,occupationTensorCoefficients_basis]
    simp only [pairLatticeCreation,LinearMap.sum_apply,weightedTranslation_single,one_mul]
    rfl
  · intro p
    change occupationTensorCoefficients n l m (mixedFiniteRawAnnihilation q n l m
      (((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) (l+1)).tensorProduct
        (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) (m+1))) (p.1,p.2)))=_
    rw [Module.Basis.tensorProduct_apply',occupationTensorCoefficients_annihilation,occupationTensorCoefficients_basis]
    simp only [pairLatticeAnnihilation,LinearMap.sum_apply,weightedTranslation_single,one_mul,sub_eq_add_neg]
    rfl
  · intro p z i hi
    have hx : z.1=shiftedOccupation n l 1 i p.1 := Subtype.ext (congrArg Prod.fst hi).symm
    have hy : z.2=shiftedOccupation n m 1 i p.2 := Subtype.ext (congrArg Prod.snd hi).symm
    dsimp only [occupationPairEmbedding]
    rw [hx,hy]
    exact mixedAnnihilation_coefficient_balance q hq hq1 n l m i p.1 p.2

/-- The physically defined contraction and the independently specified
occupation annihilation agree with the explicit positive scale. -/
theorem mixedFiniteContraction_eq_raw (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n l m : ℕ)
    (u : quantumOccupationSpace ℝ (Fin (n+1)) (l+1) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (m+1)) :
    mixedFiniteContraction q hq n l m u=
      mixedAnnihilationScale q n l m • mixedFiniteRawAnnihilation q n l m u := by
  apply mixedTensorBilin_injective q hq n l m
  apply LinearMap.ext
  intro v
  change mixedTensorBilin q n l m (mixedFiniteContraction q hq n l m u) v=
    mixedTensorBilin q n l m (mixedAnnihilationScale q n l m • mixedFiniteRawAnnihilation q n l m u) v
  rw [mixedTensorBilin_symm q n l m,← mixedFiniteContraction_adjoint,
    mixedFiniteRawAnnihilation_adjoint q hq hq1,mixedTensorBilin_symm q n l m]

end AMSPhysical
#print axioms AMSPhysical.mixedFiniteContraction_eq_raw
