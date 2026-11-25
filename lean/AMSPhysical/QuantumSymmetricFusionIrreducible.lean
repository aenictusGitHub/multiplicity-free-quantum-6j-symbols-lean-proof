import QuantumSymmetricFusionComplete
import TwoRowHighestUnique
import BilinearCyclicIrreducible

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem symmetricFusionChannelAt_irreducible (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n) (l m : ℕ)
    (r : TwoRowFusionIndex l m)
    (S : Submodule ℝ (quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m))
    (hSC : S≤symmetricFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m r)
    (hS : algebraInvariant
      (V:=quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
      (typeASymmetricTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m) S) :
    S=⊥ ∨ S=symmetricFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m r := by
  let V := quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  exact cyclic_highest_irreducible (V:=V)
    (typeASymmetricTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m)
    (symmetricTensorBilin q n l m) (symmetricTensorBilin_symm q n l m)
    (symmetricTensorBilin_definite q hq n l m)
    (typeASymmetricTensor_compact q hq hq1 n l m).adjoint_exists
    (fun i : Fin n => typeAAlgebraGenerator q n i 0) (fun i : Fin n => typeAAlgebraGenerator q n i 2)
    (fun i : Fin n =>q^(twoRowHighestWeight n hn l m r.val i)) (twoRowHighestAt q n hn l m r)
    (twoRowHighestAt_E_zero q hq hq1 n hn l m r)
    (twoRowHighestAt_K q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m r)
    (fun w hE hK => twoRowHighestAt_full_weight_unique q hq hq1 n hn l m r w hE hK) S hSC hS

end AMSPhysical
