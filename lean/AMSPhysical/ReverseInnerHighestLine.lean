import NativeInnerHighestLines
import GlobalReverseMixedPairTransfers

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem typeAHighestSpace_dynkin (q : ℝ) (n : ℕ)
    (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V) (lam : Fin n → ℤ) :
    typeAHighestSpace q n (ρ.comp (typeADynkinReflection q n)) lam =
      typeAHighestSpace q n ρ (fun i=>lam i.rev) := by
  ext v
  simp only [mem_typeAHighestSpace,AlgHom.comp_apply,typeADynkinReflection_generator]
  constructor
  · rintro ⟨hE,hK⟩
    exact ⟨fun i=>by simpa only [Fin.rev_rev] using hE i.rev,
      fun i=>by simpa only [Fin.rev_rev] using hK i.rev⟩
  · rintro ⟨hE,hK⟩
    exact ⟨fun i=>hE i.rev,fun i=>by simpa only [Fin.rev_rev] using hK i.rev⟩

theorem reverseMixedHighestSpace_finrank_one (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m : ℕ) (r : MixedFusionIndex l m) :
    Module.finrank ℝ (typeAHighestSpace
      (V:=quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
      q n (typeAReverseMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m)
      (mixedHighestDynkin n (m-r.val) (l-r.val)))=1 := by
  have he:=(highestSpaceEquiv (lam:=mixedHighestDynkin n (l-r.val) (m-r.val))
    (typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m)
    ((typeAReverseMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m).comp
      (typeADynkinReflection q n)) (mixedReflection n l m)
    (mixedReflection_intertwines q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m)).finrank_eq
  rw [typeAHighestSpace_dynkin] at he
  have hL : (fun i : Fin n=>mixedHighestDynkin n (l-r.val) (m-r.val) i.rev)=
      mixedHighestDynkin n (m-r.val) (l-r.val) := funext (mixedHighestDynkin_rev n _ _)
  rw [hL] at he
  exact he.symm.trans (mixedHighestSpace_finrank_one q hq hq1 n hn l m r)

end AMSPhysical
#print axioms AMSPhysical.reverseMixedHighestSpace_finrank_one
