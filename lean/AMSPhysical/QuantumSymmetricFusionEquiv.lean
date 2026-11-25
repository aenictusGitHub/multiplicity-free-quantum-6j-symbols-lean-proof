import QuantumSymmetricFusionOrthogonal
import QuantumSymmetricFusionIrreducible
import InvariantFamilySum
import RestrictedIrreducible

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 180000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem symmetricFusionChannelAt_invariant (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n : ℕ) (hn : 0<n) (l m : ℕ)
    (r : TwoRowFusionIndex l m) :
    algebraInvariant
      (V:=quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
      (typeASymmetricTensor q hq hD n l m) (symmetricFusionChannelAt q hq hD n hn l m r) := by
  let V := quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  exact algebraCyclicSpan_invariant (V:=V)
    (typeASymmetricTensor q hq hD n l m) (twoRowHighestAt q n hn l m r)

def symmetricFusionChannelAction (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n : ℕ) (hn : 0<n) (l m : ℕ)
    (r : TwoRowFusionIndex l m) :
    UqTypeA q n →ₐ[ℝ] Module.End ℝ (symmetricFusionChannelAt q hq hD n hn l m r) :=
  by
  let V := quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  exact invariantRepresentationRestriction (A:=UqTypeA q n) (V:=V)
    (typeASymmetricTensor q hq hD n l m) (symmetricFusionChannelAt q hq hD n hn l m r)
    (symmetricFusionChannelAt_invariant q hq hD n hn l m r)

/-- The complete physical symmetric/symmetric fusion decomposition, as an actual linear
equivalence with its independently constructed irreducible channel carriers. -/
def symmetricFusionEquiv (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n) (l m : ℕ) :
    (∀ r : TwoRowFusionIndex l m,symmetricFusionChannelAt q (ne_of_gt hq)
      (qInteger_denominator_ne_zero q hq hq1) n hn l m r) ≃ₗ[ℝ]
      (quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) := by
  classical
  let V := quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  exact orthogonalFamilyEquiv (V:=V) (symmetricTensorBilin q n l m)
    (symmetricTensorBilin_definite q hq n l m)
    (symmetricFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m)
    (fun r s hrs x hx y hy => symmetricFusionChannels_orthogonal q hq hq1 n hn l m r s hrs hy x hx)
    (symmetricFusionSpan_eq_top q hq hq1 n hn l m)

theorem symmetricFusionEquiv_isometry (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n) (l m : ℕ)
    (x y : ∀ r : TwoRowFusionIndex l m,symmetricFusionChannelAt q (ne_of_gt hq)
      (qInteger_denominator_ne_zero q hq hq1) n hn l m r) :
    symmetricTensorBilin q n l m (symmetricFusionEquiv q hq hq1 n hn l m x) (symmetricFusionEquiv q hq hq1 n hn l m y)=
      ∑ r : TwoRowFusionIndex l m,symmetricTensorBilin q n l m (x r).val (y r).val := by
  change symmetricTensorBilin q n l m
    (submoduleFamilySum (symmetricFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m) x)
    (submoduleFamilySum (symmetricFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m) y)=_
  let V := quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  exact submoduleFamilySum_isometry (V:=V) (I:=TwoRowFusionIndex l m) (symmetricTensorBilin q n l m)
    (symmetricFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m)
    (fun r s hrs u hu v hv => symmetricFusionChannels_orthogonal q hq hq1 n hn l m r s hrs hv u hu) x y

/-- The complete fusion equivalence intertwines every element of the
independently presented quantum algebra, not merely its Cartan generators. -/
theorem symmetricFusionEquiv_intertwines (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n) (l m : ℕ)
    (z : UqTypeA q n)
    (x : ∀ r : TwoRowFusionIndex l m,symmetricFusionChannelAt q (ne_of_gt hq)
      (qInteger_denominator_ne_zero q hq hq1) n hn l m r) :
    symmetricFusionEquiv q hq hq1 n hn l m
      (fun r => symmetricFusionChannelAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m r z (x r))=
      typeASymmetricTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m z
        (symmetricFusionEquiv q hq hq1 n hn l m x) := by
  exact submoduleFamilySum_intertwines
    (V:=quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
    (typeASymmetricTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m)
    (symmetricFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m)
    (symmetricFusionChannelAt_invariant q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m) z x

theorem symmetricFusionChannelAction_irreducible (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m : ℕ) (r : TwoRowFusionIndex l m)
    (S : Submodule ℝ (symmetricFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m r))
    (hS : ∀ z : UqTypeA q n,∀ v∈S,
      symmetricFusionChannelAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m r z v∈S) :
    S=⊥ ∨ S=⊤ :=
  restriction_irreducible (A:=UqTypeA q n)
    (V:=quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
    (typeASymmetricTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m)
    (symmetricFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m r)
    (symmetricFusionChannelAt_invariant q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m r)
    (symmetricFusionChannelAt_irreducible q hq hq1 n hn l m r) S
    (by simpa only [symmetricFusionChannelAction,algebraInvariant] using hS)

end AMSPhysical
#print axioms AMSPhysical.symmetricFusionEquiv_intertwines
