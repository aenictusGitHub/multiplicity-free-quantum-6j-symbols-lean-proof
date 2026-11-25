import MixedFusionHighestUnique
import EigenDisjointExpansion

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 180000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem mixedHighest_zero_of_disjoint_first_weight (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m : ℕ) (a : ℤ)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
    (hE : ∀ i : Fin n,typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      n l m (typeAAlgebraGenerator q n i 0) v=0)
    (hK : typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      n l m (typeAAlgebraGenerator q n ⟨0,hn⟩ 2) v=q^a • v)
    (hNe : ∀ r : MixedFusionIndex l m,mixedHighestDynkin n (l-r.val) (m-r.val) ⟨0,hn⟩≠a) : v=0 := by
  let V := quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  apply eigenvector_zero_of_disjoint_expansion (V:=V)
    (typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      n l m (typeAAlgebraGenerator q n ⟨0,hn⟩ 2))
    (mixedFusionHighestAt q n l m) (fun r =>q^(mixedHighestDynkin n (l-r.val) (m-r.val) ⟨0,hn⟩))
    (mixedFusionHighestAt_linearIndependent q hq n hn l m)
    (fun r =>mixedFusionHighestAt_K q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m r ⟨0,hn⟩)
    v (fun r =>mixedBoundaryFunctional n l m r v) (q^a)
    (mixedHighest_complete_expansion q hq hq1 n hn l m v hE) hK
  intro r he
  exact hNe r (zpow_right_injective₀ hq hq1 he)

theorem mixedFirstWeight_below_creation (n : ℕ) (hn : 0<n) (l m : ℕ) (r : MixedFusionIndex l m) :
    mixedHighestDynkin n (l-r.val) (m-r.val) ⟨0,hn⟩≠mixedHighestDynkin n (l+1) (m+1) ⟨0,hn⟩ := by
  have hc : (⟨0,hn⟩ : Fin n).castSucc=(0:Fin (n+1)) := Fin.ext rfl
  simp only [mixedHighestDynkin,if_pos hc,mul_one]
  by_cases hl : (⟨0,hn⟩ : Fin n).succ=Fin.last n
  · simp only [if_pos hl,mul_one]
    omega
  · simp only [if_neg hl,mul_zero,add_zero]
    omega

end AMSPhysical
