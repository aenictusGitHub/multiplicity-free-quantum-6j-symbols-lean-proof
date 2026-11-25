import QuantumSymmetricHighestExpansion
import QuantumSymmetricHighestExistence
import QuantumSymmetricMetric
import InvariantSupremum
import PositiveHighestComplete

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 200000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def symmetricFusionChannelAt (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n : ℕ) (hn : 0<n) (l m : ℕ)
    (r : TwoRowFusionIndex l m) :
    Submodule ℝ (quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) :=
  algebraCyclicSpan
    (V:=quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
    (typeASymmetricTensor q hq hD n l m) (twoRowHighestAt q n hn l m r)

def symmetricFusionSpan (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n : ℕ) (hn : 0<n) (l m : ℕ) :
    Submodule ℝ (quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) :=
  ⨆ r : TwoRowFusionIndex l m,symmetricFusionChannelAt q hq hD n hn l m r

theorem symmetricFusionSpan_invariant (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n : ℕ) (hn : 0<n) (l m : ℕ) :
    algebraInvariant
      (V:=quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
      (typeASymmetricTensor q hq hD n l m) (symmetricFusionSpan q hq hD n hn l m) := by
  let V := quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  exact algebraInvariant_iSup (V:=V) (A:=UqTypeA q n) (I:=TwoRowFusionIndex l m)
    (typeASymmetricTensor q hq hD n l m) (symmetricFusionChannelAt q hq hD n hn l m)
    (fun r => algebraCyclicSpan_invariant (V:=V)
      (typeASymmetricTensor q hq hD n l m) (twoRowHighestAt q n hn l m r))

theorem symmetricHighest_mem_fusionSpan (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n) (l m : ℕ)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
    (hE : ∀ i : Fin n,typeASymmetricTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      n l m (typeAAlgebraGenerator q n i 0) v=0) :
    v∈symmetricFusionSpan q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m := by
  rw [symmetricHighest_complete_expansion q hq hq1 n hn l m v hE]
  apply Submodule.sum_mem
  intro r hr
  apply Submodule.smul_mem
  exact (le_iSup (symmetricFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m) r)
    (algebraCyclicSpan_self _ _)

/-- The constructed actual two-row channels exhaust the whole physical
symmetric/symmetric tensor product in every rank and degree. -/
theorem symmetricFusionSpan_eq_top (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n) (l m : ℕ) :
    symmetricFusionSpan q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m=⊤ := by
  let V := quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  let S : Submodule ℝ V := symmetricFusionSpan q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m
  let B : LinearMap.BilinForm ℝ V := symmetricTensorBilin q n l m
  apply positive_invariant_complete_of_highest (V:=V)
    (typeASymmetricTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m)
    B (symmetricTensorBilin_symm q n l m) (symmetricTensorBilin_definite q hq n l m)
    (typeASymmetricTensor_compact q hq hq1 n l m).adjoint_exists
    (fun w : V => ∀ i : Fin n,typeASymmetricTensor q (ne_of_gt hq)
      (qInteger_denominator_ne_zero q hq hq1) n l m (typeAAlgebraGenerator q n i 0) w=0)
    S (symmetricFusionSpan_invariant q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m)
    (fun w => symmetricHighest_mem_fusionSpan q hq hq1 n hn l m w)
  intro T hT hT0
  exact symmetricInvariant_exists_highest q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m T hT hT0

end AMSPhysical
#print axioms AMSPhysical.symmetricFusionSpan_eq_top
