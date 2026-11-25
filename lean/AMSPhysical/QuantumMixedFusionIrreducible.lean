import QuantumMixedFusionComplete
import QuantumMixedIrreducible

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2600000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem mixedFusionHighest_cyclic_irreducible (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l m r : ℕ) (hrl : r≤l) (hrm : r≤m)
    (S : Submodule ℝ (quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m))
    (hSC : S≤algebraCyclicSpan
      (V:=quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
      (typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m)
      (mixedFusionHighest q n l m r hrl hrm))
    (hS : algebraInvariant
      (V:=quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
      (typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m) S) :
    S=⊥ ∨ S=algebraCyclicSpan
      (V:=quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
      (typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m)
      (mixedFusionHighest q n l m r hrl hrm) := by
  obtain ⟨a,ha⟩ := Nat.exists_eq_add_of_le hrl
  obtain ⟨b,hb⟩ := Nat.exists_eq_add_of_le hrm
  subst l
  subst m
  rw [mixedFusionHighest_add] at hSC ⊢
  exact mixedChannelSubmodule_irreducible q hq hq1 n r a b hn S hSC hS

theorem mixedFusionChannelAt_irreducible (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n) (l m : ℕ)
    (r : MixedFusionIndex l m)
    (S : Submodule ℝ (quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m))
    (hSC : S≤mixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m r)
    (hS : algebraInvariant
      (V:=quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
      (typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m) S) :
    S=⊥ ∨ S=mixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m r :=
  mixedFusionHighest_cyclic_irreducible q hq hq1 n hn l m r.val _ _ S hSC hS

end AMSPhysical
