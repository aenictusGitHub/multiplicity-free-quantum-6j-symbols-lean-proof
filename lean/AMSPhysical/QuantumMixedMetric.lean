import QuantumMixedNonzero
import QuantumTypeACompact
import QuantumOppositeModuleCompact
import TensorWeightedHilbert
import WeightedBasisSum

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def mixedTensorBilin (q : ℝ) (n l m : ℕ) :
    (quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) →ₗ[ℝ]
    (quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) →ₗ[ℝ] ℝ :=
  tensorWeightedBilin (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l)
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m)
    (occupationCompactWeight q n l) (occupationOppositeWeight q n m)

def mixedTensorNormed (q : ℝ) (hq : 0<q) (n l m : ℕ) :
    NormedAddCommGroup (quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) :=
  finiteWeightedNormedAddCommGroup
    (V:=quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
    (ι:=occupationWeights (Fin (n+1)) l × occupationWeights (Fin (n+1)) m)
    (fun xy => occupationCompactWeight q n l xy.1*occupationOppositeWeight q n m xy.2)
    (fun xy => mul_pos (occupationCompactWeight_pos q hq n l xy.1) (occupationOppositeWeight_pos q hq n m xy.2))
    ((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l).tensorProduct
      (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m)).equivFun.toLinearMap
    ((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l).tensorProduct
      (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m)).equivFun.injective

theorem mixedHighestVector_norm_sum (q : ℝ) (n r a b : ℕ) :
    mixedTensorBilin q n (r+a) (r+b) (mixedHighestVector q n r a b) (mixedHighestVector q n r a b)=
      ∑ t : occupationWeights (Fin (n+1)) r,(mixedHighestCoefficient q n r b t)^2*
        occupationCompactWeight q n (r+a) (shiftedOccupation n r a 0 t)*
        occupationOppositeWeight q n (r+b) (shiftedOccupation n r b (Fin.last n) t) := by
  classical
  let e : occupationWeights (Fin (n+1)) r →
      occupationWeights (Fin (n+1)) (r+a) × occupationWeights (Fin (n+1)) (r+b) :=
    fun t => (shiftedOccupation n r a 0 t,shiftedOccupation n r b (Fin.last n) t)
  have he : Function.Injective e := by
    intro x y h
    exact shiftedOccupation_injective n r a 0 (congrArg Prod.fst h)
  have hv : mixedHighestVector q n r a b=
      ∑ t : occupationWeights (Fin (n+1)) r,mixedHighestCoefficient q n r b t •
        ((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) (r+a)).tensorProduct
          (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) (r+b))) (e t) := by
    unfold mixedHighestVector
    apply Finset.sum_congr rfl
    intro t ht
    rw [Module.Basis.tensorProduct_apply']
    rfl
  rw [hv]
  have hh := finiteWeightedPair_sum_basis
    (V:=quantumOccupationSpace ℝ (Fin (n+1)) (r+a) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (r+b))
    ((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) (r+a)).tensorProduct
      (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) (r+b)))
    (fun xy => occupationCompactWeight q n (r+a) xy.1*occupationOppositeWeight q n (r+b) xy.2)
    e he (mixedHighestCoefficient q n r b)
  change mixedTensorBilin q n (r+a) (r+b) _ _=_ at hh
  rw [hh]
  apply Finset.sum_congr rfl
  intro t ht
  dsimp [e]
  ring

end AMSPhysical
#print axioms AMSPhysical.mixedHighestVector_norm_sum
