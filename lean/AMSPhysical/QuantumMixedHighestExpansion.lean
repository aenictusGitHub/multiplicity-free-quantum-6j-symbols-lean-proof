import QuantumMixedFusionIndex
import QuantumMixedBoundarySupport

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

/-- COMPLETE classification of the actual mixed highest space. Every
highest vector, without an assumed Cartan weight or support, has this
unique explicit expansion in exactly min(l,m)+1 constructed channels. -/
theorem mixedHighest_complete_expansion (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n) (l m : ℕ)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
    (hE : ∀ i : Fin n,typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      n l m (typeAAlgebraGenerator q n i 0) v=0) :
    v=∑ r : MixedFusionIndex l m,
      occupationTensorCoefficients n l m v ((highestOccupation n l).val,(mixedBoundaryAt n l m r).val) •
        mixedFusionHighestAt q n l m r := by
  classical
  apply sub_eq_zero.mp
  apply mixedHighest_zero_of_boundary q hq hq1 n l m
  · intro i
    rw [map_sub,hE,map_sum]
    simp only [map_smul,mixedFusionHighestAt_E_zero q hq hq1,smul_zero,Finset.sum_const_zero,sub_self]
  · intro y
    rw [map_sub,Finsupp.sub_apply,map_sum]
    simp only [Finsupp.coe_finset_sum,Finset.sum_apply]
    apply sub_eq_zero.mpr
    simp only [map_smul,Finsupp.smul_apply,smul_eq_mul,mixedFusionHighestAt_boundary q hq n hn]
    by_cases hex : ∃ r : MixedFusionIndex l m,mixedBoundaryAt n l m r=y
    · obtain ⟨r,hr⟩ := hex
      rw [Finset.sum_eq_single r]
      · rw [if_pos hr,mul_one,hr]
      · intro s hs hsr
        have hne : mixedBoundaryAt n l m s≠y := by
          intro he
          apply hsr
          exact mixedBoundaryAt_injective n l m hn (he.trans hr.symm)
        rw [if_neg hne,mul_zero]
      · simp
    · have hnone : ∀ r : MixedFusionIndex l m,mixedBoundaryAt n l m r≠y := by
        intro r h
        exact hex ⟨r,h⟩
      have hsum : (∑ r : MixedFusionIndex l m,
          occupationTensorCoefficients n l m v ((highestOccupation n l).val,(mixedBoundaryAt n l m r).val)*
            (if mixedBoundaryAt n l m r=y then 1 else 0))=0 := by
        apply Finset.sum_eq_zero
        intro r hr
        rw [if_neg (hnone r),mul_zero]
      rw [hsum]
      by_contra hc
      obtain ⟨r,hrl,hrm,hy⟩ := mixedHighest_boundary_support q hq hq1 n hn l m v hE y hc
      let t : MixedFusionIndex l m := ⟨r,by omega⟩
      apply hex
      exact ⟨t,hy.symm⟩

end AMSPhysical
#print axioms AMSPhysical.mixedHighest_complete_expansion
