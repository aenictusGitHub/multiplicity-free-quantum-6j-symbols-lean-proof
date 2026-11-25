import ActualCarrierEquivalences
import MixedFusionHighestUnique
import TwoRowHighestUnique
import QuantumMixedFusionOrthogonal

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem highestSpace_finrank_one_of_unique {q : ℝ} {n : ℕ}
    (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V) (lam : Fin n → ℤ) (v : V)
    (hv : v∈typeAHighestSpace q n ρ lam) (hn : v≠0)
    (hSpan : ∀ w∈typeAHighestSpace q n ρ lam,∃ a : ℝ,w=a • v) :
    Module.finrank ℝ (typeAHighestSpace q n ρ lam)=1 := by
  have he : typeAHighestSpace q n ρ lam=Submodule.span ℝ {v} := by
    apply le_antisymm
    · intro w hw
      obtain ⟨a,rfl⟩:=hSpan w hw
      exact Submodule.smul_mem _ a (Submodule.subset_span (Set.mem_singleton v))
    · exact Submodule.span_le.mpr (by intro w hw;rcases Set.mem_singleton_iff.mp hw with rfl;exact hv)
  rw [he]
  exact finrank_span_singleton hn

theorem mixedHighestSpace_finrank_one (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m : ℕ) (r : MixedFusionIndex l m) :
    Module.finrank ℝ (typeAHighestSpace (V:=quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ]
      quantumOccupationSpace ℝ (Fin (n+1)) m) q n
      (typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m)
      (mixedHighestDynkin n (l-r.val) (m-r.val)))=1 := by
  apply highestSpace_finrank_one_of_unique _ _ (mixedFusionHighestAt q n l m r)
  · exact (mem_typeAHighestSpace q n _ _ _).mpr
      ⟨mixedFusionHighestAt_E_zero q hq hq1 n l m r,
        mixedFusionHighestAt_K q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m r⟩
  · exact mixedFusionHighestAt_ne_zero q hq n hn l m r
  · intro v hv
    obtain ⟨hE,hK⟩:=(mem_typeAHighestSpace q n _ _ v).mp hv
    exact ⟨mixedBoundaryFunctional n l m r v,
      mixedFusionHighestAt_full_weight_unique q hq hq1 n hn l m r v hE hK⟩

theorem twoRowHighestSpace_finrank_one (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m : ℕ) (r : TwoRowFusionIndex l m) :
    Module.finrank ℝ (typeAHighestSpace (V:=quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ]
      quantumOccupationSpace ℝ (Fin (n+1)) m) q n
      (typeASymmetricTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m)
      (twoRowHighestWeight n hn l m r.val))=1 := by
  apply highestSpace_finrank_one_of_unique _ _ (twoRowHighestAt q n hn l m r)
  · exact (mem_typeAHighestSpace q n _ _ _).mpr
      ⟨twoRowHighestAt_E_zero q hq hq1 n hn l m r,
        twoRowHighestAt_K q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m r⟩
  · intro he
    have hb:=twoRowHighestAt_boundary q n hn l m r (twoRowBoundaryAt n hn l m r)
    simp only [he,map_zero,Finsupp.zero_apply,if_pos rfl] at hb
    norm_num at hb
  · intro v hv
    obtain ⟨hE,hK⟩:=(mem_typeAHighestSpace q n _ _ v).mp hv
    exact twoRowHighestAt_full_weight_unique q hq hq1 n hn l m r v hE hK

end AMSPhysical
#print axioms AMSPhysical.mixedHighestSpace_finrank_one
#print axioms AMSPhysical.twoRowHighestSpace_finrank_one
