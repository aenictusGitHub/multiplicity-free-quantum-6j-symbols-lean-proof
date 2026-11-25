import CyclicEigenHomCoordinates
import MixedFusionHighestUnique
import QuantumMixedFusionComplete

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def MixedHomMatchIndex (n : ℕ) (hn : 0<n) (a b l m : ℕ) :=
  MatchingWeightPair
    (fun r : MixedFusionIndex a b =>mixedHighestDynkin n (a-r.val) (b-r.val) ⟨0,hn⟩)
    (fun s : MixedFusionIndex l m =>mixedHighestDynkin n (l-s.val) (m-s.val) ⟨0,hn⟩)

instance mixedHomMatchIndexFintype (n : ℕ) (hn : 0<n) (a b l m : ℕ) : Fintype (MixedHomMatchIndex n hn a b l m) :=
  inferInstanceAs (Fintype (MatchingWeightPair _ _))

def mixedHomCoordinates (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n : ℕ) (hn : 0<n) (a b l m : ℕ) :
    algebraIntertwinerSpace
      (V:=quantumOccupationSpace ℝ (Fin (n+1)) a ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) b)
      (W:=quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
      (typeAMixedTensor q hq hD n a b) (typeAMixedTensor q hq hD n l m) →ₗ[ℝ]
      (MixedHomMatchIndex n hn a b l m → ℝ) := by
  let V := quantumOccupationSpace ℝ (Fin (n+1)) a ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) b
  let W := quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  letI : AddCommGroup W := inferInstance
  letI : Module ℝ W := inferInstance
  exact cyclicEigenHomCoordinates (V:=V) (W:=W)
    (typeAMixedTensor q hq hD n a b) (typeAMixedTensor q hq hD n l m)
    (mixedFusionHighestAt q n a b) (mixedBoundaryFunctional n l m)
    (fun r =>mixedHighestDynkin n (a-r.val) (b-r.val) ⟨0,hn⟩)
    (fun s =>mixedHighestDynkin n (l-s.val) (m-s.val) ⟨0,hn⟩)

/-- A proved injection of the actual full quantum-group pair Hom space into
one scalar for each matching physical intermediate highest weight. -/
theorem mixedHomCoordinates_injective (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (a b l m : ℕ) :
    Function.Injective (mixedHomCoordinates q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn a b l m) := by
  let V := quantumOccupationSpace ℝ (Fin (n+1)) a ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) b
  let W := quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  letI : AddCommGroup W := inferInstance
  letI : Module ℝ W := inferInstance
  apply cyclicEigenHomCoordinates_injective (V:=V) (W:=W)
    (typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b)
    (typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m)
    (mixedFusionHighestAt q n a b) (mixedFusionHighestAt q n l m) (mixedBoundaryFunctional n l m)
    (fun r =>mixedHighestDynkin n (a-r.val) (b-r.val) ⟨0,hn⟩)
    (fun s =>mixedHighestDynkin n (l-s.val) (m-s.val) ⟨0,hn⟩)
    (fun x : ℤ =>q^x) (zpow_right_injective₀ hq hq1) (typeAAlgebraGenerator q n ⟨0,hn⟩ 2)
  · exact mixedFusionSpan_eq_top q hq hq1 n hn a b
  · exact mixedFusionHighestAt_linearIndependent q hq n hn l m
  · intro r
    exact mixedFusionHighestAt_K q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b r ⟨0,hn⟩
  · intro s
    exact mixedFusionHighestAt_K q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m s ⟨0,hn⟩
  · intro f r
    apply mixedHighest_complete_expansion q hq hq1 n hn l m (f.val (mixedFusionHighestAt q n a b r))
    intro i
    rw [← f.property,mixedFusionHighestAt_E_zero q hq hq1,map_zero]

end AMSPhysical
#print axioms AMSPhysical.mixedHomCoordinates_injective
