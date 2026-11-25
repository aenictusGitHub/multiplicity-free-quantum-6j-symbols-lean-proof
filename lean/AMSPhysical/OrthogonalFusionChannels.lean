import OrthogonalFusionTransport

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
variable {V W I : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  [Fintype I] [DecidableEq I]
variable
    (B : LinearMap.BilinForm ℝ V) (C : LinearMap.BilinForm ℝ W)
    (hB : ∀ v,B v v=0 → v=0) (hC : ∀ w,C w w=0 → w=0)
    (S : I → Submodule ℝ V) (T : I → Submodule ℝ W)
    (hS : ∀ i j,i≠j → ∀ x∈S i,∀ y∈S j,B x y=0)
    (hT : ∀ i j,i≠j → ∀ x∈T i,∀ y∈T j,C x y=0)
    (hSS : (⨆ i,S i)=⊤) (hTT : (⨆ i,T i)=⊤)
    (e : ∀ i,S i ≃ₗ[ℝ] T i)

theorem orthogonalFusionTransport_channel_apply (i : I) (x : S i) :
    orthogonalFusionTransport B C hB hC S T hS hT hSS hTT e x.val=(e i x).val := by
  have he:=orthogonalFusionTransport_sum B C hB hC S T hS hT hSS hTT e (Pi.single i x)
  rw [submoduleFamilySum_single] at he
  rw [he]
  change (∑ j,(e j ((Pi.single i x : ∀ j,S j) j)).val)=(e i x).val
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.single_apply,hji,Ne.symm hji]
  · simp

theorem orthogonalFusionTransport_channel_map (i : I) :
    (S i).map (orthogonalFusionTransport B C hB hC S T hS hT hSS hTT e).toLinearMap=T i := by
  ext w
  constructor
  · rintro ⟨v,hv,rfl⟩
    change orthogonalFusionTransport B C hB hC S T hS hT hSS hTT e v∈T i
    rw [orthogonalFusionTransport_channel_apply B C hB hC S T hS hT hSS hTT e i ⟨v,hv⟩]
    exact (e i ⟨v,hv⟩).property
  · intro hw
    refine ⟨((e i).symm ⟨w,hw⟩).val,((e i).symm ⟨w,hw⟩).property,?_⟩
    change orthogonalFusionTransport B C hB hC S T hS hT hSS hTT e ((e i).symm ⟨w,hw⟩).val=w
    rw [orthogonalFusionTransport_channel_apply,LinearEquiv.apply_symm_apply]

end AMSPhysical
#print axioms AMSPhysical.orthogonalFusionTransport_channel_map
