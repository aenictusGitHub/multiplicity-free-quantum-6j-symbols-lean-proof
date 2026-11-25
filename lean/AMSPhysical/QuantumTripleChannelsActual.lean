import QuantumTripleGeneralChannels
import QuantumMixedZeroExternalChannels

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem tensorSubtypeTop_range_left {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W] :
    LinearMap.range (TensorProduct.map (⊤ : Submodule ℝ V).subtype (LinearMap.id : Module.End ℝ W))=⊤ := by
  apply LinearMap.range_eq_top.mpr
  exact TensorProduct.map_surjective (fun v =>⟨⟨v,trivial⟩,rfl⟩) Function.surjective_id

theorem tensorSubtypeTop_range_right {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W] :
    LinearMap.range (TensorProduct.map (LinearMap.id : Module.End ℝ V) (⊤ : Submodule ℝ W).subtype)=⊤ := by
  apply LinearMap.range_eq_top.mpr
  exact TensorProduct.map_surjective Function.surjective_id (fun w =>⟨⟨w,trivial⟩,rfl⟩)

/-- The boundary-complete channel definition equals the tensor image of the
actual irreducible mixed summand in EVERY degree, including zero degrees. -/
theorem physicalTripleLeftChannelGeneral_actual (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m c : ℕ) (r : MixedFusionIndex l m) :
    physicalTripleLeftChannelGeneral q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m c r=
      (LinearMap.range (TensorProduct.map
        (mixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m r).subtype
        (LinearMap.id : Module.End ℝ (quantumOccupationSpace ℝ (Fin (n+1)) c)))).map
          (TensorProduct.assoc ℝ _ _ _).toLinearMap := by
  cases l with
  | zero =>
    rw [mixedFusionChannel_zero_left_top q hq hq1 n hn,tensorSubtypeTop_range_left,Submodule.map_top]
    exact ((TensorProduct.assoc ℝ _ _ _).range).symm
  | succ l =>
    cases m with
    | zero =>
      rw [mixedFusionChannel_zero_right_top q hq hq1 n hn,tensorSubtypeTop_range_left,Submodule.map_top]
      exact ((TensorProduct.assoc ℝ _ _ _).range).symm
    | succ m => rfl

theorem physicalTripleRightChannelGeneral_actual (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m c : ℕ) (r : MixedFusionIndex m c) :
    physicalTripleRightChannelGeneral q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m c r=
      LinearMap.range (TensorProduct.map (LinearMap.id : Module.End ℝ (quantumOccupationSpace ℝ (Fin (n+1)) l))
        (reverseMixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n m c r).subtype) := by
  cases m with
  | zero =>
    rw [reverseMixedFusionChannel_zero_left_top q hq hq1 n hn,tensorSubtypeTop_range_right]
    rfl
  | succ m =>
    cases c with
    | zero =>
      rw [reverseMixedFusionChannel_zero_right_top q hq hq1 n hn,tensorSubtypeTop_range_right]
      rfl
    | succ c => rfl

end AMSPhysical
#print axioms AMSPhysical.physicalTripleLeftChannelGeneral_actual
#print axioms AMSPhysical.physicalTripleRightChannelGeneral_actual
