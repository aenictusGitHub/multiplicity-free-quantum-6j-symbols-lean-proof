import QuantumMixedFusionOrthogonal
import QuantumMixedFusionIrreducible
import InvariantFamilySum
import RestrictedIrreducible

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 180000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem mixedFusionChannelAt_invariant (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n l m : ℕ)
    (r : MixedFusionIndex l m) :
    algebraInvariant
      (V:=quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
      (typeAMixedTensor q hq hD n l m) (mixedFusionChannelAt q hq hD n l m r) := by
  let V := quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  exact algebraCyclicSpan_invariant (V:=V)
    (typeAMixedTensor q hq hD n l m) (mixedFusionHighestAt q n l m r)

def mixedFusionChannelAction (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n l m : ℕ)
    (r : MixedFusionIndex l m) :
    UqTypeA q n →ₐ[ℝ] Module.End ℝ (mixedFusionChannelAt q hq hD n l m r) :=
  by
  let V := quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  exact invariantRepresentationRestriction (A:=UqTypeA q n) (V:=V)
    (typeAMixedTensor q hq hD n l m) (mixedFusionChannelAt q hq hD n l m r)
    (mixedFusionChannelAt_invariant q hq hD n l m r)

/-- The complete physical mixed fusion decomposition, as an actual linear
equivalence with its independently constructed irreducible channel carriers. -/
def mixedFusionEquiv (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n) (l m : ℕ) :
    (∀ r : MixedFusionIndex l m,mixedFusionChannelAt q (ne_of_gt hq)
      (qInteger_denominator_ne_zero q hq hq1) n l m r) ≃ₗ[ℝ]
      (quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) := by
  classical
  let V := quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  exact orthogonalFamilyEquiv (V:=V) (mixedTensorBilin q n l m)
    (mixedTensorBilin_definite q hq n l m)
    (mixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m)
    (fun r s hrs x hx y hy => mixedFusionChannels_orthogonal q hq hq1 n hn l m r s hrs hy x hx)
    (mixedFusionSpan_eq_top q hq hq1 n hn l m)

theorem mixedFusionEquiv_isometry (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n) (l m : ℕ)
    (x y : ∀ r : MixedFusionIndex l m,mixedFusionChannelAt q (ne_of_gt hq)
      (qInteger_denominator_ne_zero q hq hq1) n l m r) :
    mixedTensorBilin q n l m (mixedFusionEquiv q hq hq1 n hn l m x) (mixedFusionEquiv q hq hq1 n hn l m y)=
      ∑ r : MixedFusionIndex l m,mixedTensorBilin q n l m (x r).val (y r).val := by
  change mixedTensorBilin q n l m
    (submoduleFamilySum (mixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m) x)
    (submoduleFamilySum (mixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m) y)=_
  let V := quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  exact submoduleFamilySum_isometry (V:=V) (I:=MixedFusionIndex l m) (mixedTensorBilin q n l m)
    (mixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m)
    (fun r s hrs u hu v hv => mixedFusionChannels_orthogonal q hq hq1 n hn l m r s hrs hv u hu) x y

/-- The complete fusion equivalence intertwines every element of the
independently presented quantum algebra, not merely its Cartan generators. -/
theorem mixedFusionEquiv_intertwines (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n) (l m : ℕ)
    (z : UqTypeA q n)
    (x : ∀ r : MixedFusionIndex l m,mixedFusionChannelAt q (ne_of_gt hq)
      (qInteger_denominator_ne_zero q hq hq1) n l m r) :
    mixedFusionEquiv q hq hq1 n hn l m
      (fun r => mixedFusionChannelAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m r z (x r))=
      typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m z
        (mixedFusionEquiv q hq hq1 n hn l m x) := by
  exact submoduleFamilySum_intertwines
    (V:=quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
    (typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m)
    (mixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m)
    (mixedFusionChannelAt_invariant q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m) z x

theorem mixedFusionChannelAction_irreducible (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m : ℕ) (r : MixedFusionIndex l m)
    (S : Submodule ℝ (mixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m r))
    (hS : ∀ z : UqTypeA q n,∀ v∈S,
      mixedFusionChannelAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m r z v∈S) :
    S=⊥ ∨ S=⊤ :=
  restriction_irreducible (A:=UqTypeA q n)
    (V:=quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
    (typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m)
    (mixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m r)
    (mixedFusionChannelAt_invariant q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m r)
    (mixedFusionChannelAt_irreducible q hq hq1 n hn l m r) S
    (by simpa only [mixedFusionChannelAction,algebraInvariant] using hS)

end AMSPhysical
#print axioms AMSPhysical.mixedFusionEquiv_intertwines
