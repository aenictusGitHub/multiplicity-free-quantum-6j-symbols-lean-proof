import QuantumMixedFusionIndex

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem mixedFusionHighest_K (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n l m r : ℕ)
    (hrl : r≤l) (hrm : r≤m) (i : Fin n) :
    typeAMixedTensor q hq hD n l m (typeAAlgebraGenerator q n i 2) (mixedFusionHighest q n l m r hrl hrm)=
      q^(mixedHighestDynkin n (l-r) (m-r) i) • mixedFusionHighest q n l m r hrl hrm := by
  obtain ⟨a,ha⟩ := Nat.exists_eq_add_of_le hrl
  obtain ⟨b,hb⟩ := Nat.exists_eq_add_of_le hrm
  subst l
  subst m
  rw [mixedFusionHighest_add]
  simp only [Nat.add_sub_cancel_left]
  exact mixedHighestVector_K q hq hD n r a b i

theorem mixedFusionHighestAt_K (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n l m : ℕ)
    (r : MixedFusionIndex l m) (i : Fin n) :
    typeAMixedTensor q hq hD n l m (typeAAlgebraGenerator q n i 2) (mixedFusionHighestAt q n l m r)=
      q^(mixedHighestDynkin n (l-r.val) (m-r.val) i) • mixedFusionHighestAt q n l m r :=
  mixedFusionHighest_K q hq hD n l m r.val _ _ i

theorem mixedFusionHighest_first_weight_injective (n : ℕ) (hn : 0<n) (l m : ℕ) :
    Function.Injective (fun r : MixedFusionIndex l m =>
      mixedHighestDynkin n (l-r.val) (m-r.val) (⟨0,hn⟩ : Fin n)) := by
  intro r s he
  have hr := r.isLt
  have hs := s.isLt
  apply Fin.ext
  have hc : (⟨0,hn⟩ : Fin n).castSucc=(0:Fin (n+1)) := Fin.ext rfl
  dsimp only at he
  simp only [mixedHighestDynkin,if_pos hc,mul_one] at he
  by_cases hlast : (⟨0,hn⟩ : Fin n).succ=Fin.last n
  · simp only [if_pos hlast,mul_one] at he
    omega
  · simp only [if_neg hlast,mul_zero,add_zero] at he
    omega

end AMSPhysical
