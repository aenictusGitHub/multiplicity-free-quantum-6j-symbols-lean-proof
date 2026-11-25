import QuantumMixedHighestExpansion
import QuantumMixedHighestExistence
import QuantumMixedCompact
import InvariantSupremum
import PositiveHighestComplete

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 180000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def mixedFusionChannelAt (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n l m : ℕ) (r : MixedFusionIndex l m) :
    Submodule ℝ (quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) :=
  algebraCyclicSpan
    (V:=quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
    (typeAMixedTensor q hq hD n l m) (mixedFusionHighestAt q n l m r)

def mixedFusionSpan (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n l m : ℕ) :
    Submodule ℝ (quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) :=
  ⨆ r : MixedFusionIndex l m,mixedFusionChannelAt q hq hD n l m r

theorem mixedFusionSpan_invariant (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n l m : ℕ) :
    algebraInvariant
      (V:=quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
      (typeAMixedTensor q hq hD n l m) (mixedFusionSpan q hq hD n l m) := by
  let V := quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  exact algebraInvariant_iSup (V:=V) (A:=UqTypeA q n) (I:=MixedFusionIndex l m)
    (typeAMixedTensor q hq hD n l m) (mixedFusionChannelAt q hq hD n l m)
    (fun r => algebraCyclicSpan_invariant
      (V:=quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
      (typeAMixedTensor q hq hD n l m) (mixedFusionHighestAt q n l m r))

theorem mixedHighest_mem_fusionSpan (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n) (l m : ℕ)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
    (hE : ∀ i : Fin n,typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      n l m (typeAAlgebraGenerator q n i 0) v=0) :
    v∈mixedFusionSpan q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m := by
  rw [mixedHighest_complete_expansion q hq hq1 n hn l m v hE]
  apply Submodule.sum_mem
  intro r hr
  apply Submodule.smul_mem
  exact (le_iSup (mixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m) r)
    (algebraCyclicSpan_self _ _)

/-- FULL mixed tensor-product completeness, derived from actual generator
actions, complete highest-space classification and positive orthogonal
complements. No Littlewood-Richardson or semisimplicity axiom is assumed. -/
theorem mixedFusionSpan_eq_top (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n) (l m : ℕ) :
    mixedFusionSpan q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m=⊤ := by
  let V := quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  let S : Submodule ℝ V := mixedFusionSpan q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m
  let B : LinearMap.BilinForm ℝ V := mixedTensorBilin q n l m
  apply positive_invariant_complete_of_highest (V:=V)
    (typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m)
    B (mixedTensorBilin_symm q n l m) (mixedTensorBilin_definite q hq n l m)
    (typeAMixedTensor_compact q hq hq1 n l m).adjoint_exists
    (fun w : V => ∀ i : Fin n,typeAMixedTensor q (ne_of_gt hq)
      (qInteger_denominator_ne_zero q hq hq1) n l m (typeAAlgebraGenerator q n i 0) w=0)
    S (mixedFusionSpan_invariant q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m)
    (fun w => mixedHighest_mem_fusionSpan q hq hq1 n hn l m w)
  intro T hT hT0
  exact mixedInvariant_exists_highest q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m T hT hT0

end AMSPhysical
#print axioms AMSPhysical.mixedFusionSpan_eq_top
