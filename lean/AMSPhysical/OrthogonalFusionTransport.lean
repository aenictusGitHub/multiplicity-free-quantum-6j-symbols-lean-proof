import InvariantFamilySum

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
variable {A V W I : Type*} [Ring A] [Algebra ℝ A]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  [Fintype I] [DecidableEq I]

/-- Assemble independently proved channel equivalences into an equivalence
of the complete physical modules using their orthogonal decompositions. -/
def orthogonalFusionTransport
    (B : LinearMap.BilinForm ℝ V) (C : LinearMap.BilinForm ℝ W)
    (hB : ∀ v,B v v=0 → v=0) (hC : ∀ w,C w w=0 → w=0)
    (S : I → Submodule ℝ V) (T : I → Submodule ℝ W)
    (hS : ∀ i j,i≠j → ∀ x∈S i,∀ y∈S j,B x y=0)
    (hT : ∀ i j,i≠j → ∀ x∈T i,∀ y∈T j,C x y=0)
    (hSS : (⨆ i,S i)=⊤) (hTT : (⨆ i,T i)=⊤)
    (e : ∀ i,S i ≃ₗ[ℝ] T i) : V ≃ₗ[ℝ] W :=
  (orthogonalFamilyEquiv B hB S hS hSS).symm.trans
    ((LinearEquiv.piCongrRight e).trans (orthogonalFamilyEquiv C hC T hT hTT))

theorem orthogonalFusionTransport_sum
    (B : LinearMap.BilinForm ℝ V) (C : LinearMap.BilinForm ℝ W)
    (hB : ∀ v,B v v=0 → v=0) (hC : ∀ w,C w w=0 → w=0)
    (S : I → Submodule ℝ V) (T : I → Submodule ℝ W)
    (hS : ∀ i j,i≠j → ∀ x∈S i,∀ y∈S j,B x y=0)
    (hT : ∀ i j,i≠j → ∀ x∈T i,∀ y∈T j,C x y=0)
    (hSS : (⨆ i,S i)=⊤) (hTT : (⨆ i,T i)=⊤)
    (e : ∀ i,S i ≃ₗ[ℝ] T i) (x : ∀ i,S i) :
    orthogonalFusionTransport B C hB hC S T hS hT hSS hTT e (submoduleFamilySum S x)=
      submoduleFamilySum T (fun i =>e i (x i)) := by
  change (orthogonalFamilyEquiv C hC T hT hTT)
    ((LinearEquiv.piCongrRight e) ((orthogonalFamilyEquiv B hB S hS hSS).symm
      ((orthogonalFamilyEquiv B hB S hS hSS) x)))=_
  rw [LinearEquiv.symm_apply_apply]
  rfl

theorem orthogonalFusionTransport_isometry
    (B : LinearMap.BilinForm ℝ V) (C : LinearMap.BilinForm ℝ W)
    (hB : ∀ v,B v v=0 → v=0) (hC : ∀ w,C w w=0 → w=0)
    (S : I → Submodule ℝ V) (T : I → Submodule ℝ W)
    (hS : ∀ i j,i≠j → ∀ x∈S i,∀ y∈S j,B x y=0)
    (hT : ∀ i j,i≠j → ∀ x∈T i,∀ y∈T j,C x y=0)
    (hSS : (⨆ i,S i)=⊤) (hTT : (⨆ i,T i)=⊤)
    (e : ∀ i,S i ≃ₗ[ℝ] T i)
    (he : ∀ i (x y : S i),C (e i x).val (e i y).val=B x.val y.val) (v w : V) :
    C (orthogonalFusionTransport B C hB hC S T hS hT hSS hTT e v)
      (orthogonalFusionTransport B C hB hC S T hS hT hSS hTT e w)=B v w := by
  obtain ⟨x,rfl⟩:=submoduleFamilySum_surjective S hSS v
  obtain ⟨y,rfl⟩:=submoduleFamilySum_surjective S hSS w
  rw [orthogonalFusionTransport_sum,orthogonalFusionTransport_sum,
    submoduleFamilySum_isometry C T hT,submoduleFamilySum_isometry B S hS]
  exact Finset.sum_congr rfl (fun i _ =>he i (x i) (y i))

theorem orthogonalFusionTransport_intertwines
    (B : LinearMap.BilinForm ℝ V) (C : LinearMap.BilinForm ℝ W)
    (hB : ∀ v,B v v=0 → v=0) (hC : ∀ w,C w w=0 → w=0)
    (S : I → Submodule ℝ V) (T : I → Submodule ℝ W)
    (hS : ∀ i j,i≠j → ∀ x∈S i,∀ y∈S j,B x y=0)
    (hT : ∀ i j,i≠j → ∀ x∈T i,∀ y∈T j,C x y=0)
    (hSS : (⨆ i,S i)=⊤) (hTT : (⨆ i,T i)=⊤)
    (e : ∀ i,S i ≃ₗ[ℝ] T i)
    (ρ : A →ₐ[ℝ] Module.End ℝ V) (σ : A →ₐ[ℝ] Module.End ℝ W)
    (hρ : ∀ i,algebraInvariant ρ (S i)) (hσ : ∀ i,algebraInvariant σ (T i))
    (he : ∀ i z (x : S i),(e i ⟨ρ z x.val,hρ i z x.val x.property⟩).val=σ z (e i x).val)
    (z : A) (v : V) :
    orthogonalFusionTransport B C hB hC S T hS hT hSS hTT e (ρ z v)=
      σ z (orthogonalFusionTransport B C hB hC S T hS hT hSS hTT e v) := by
  obtain ⟨x,rfl⟩:=submoduleFamilySum_surjective S hSS v
  rw [← submoduleFamilySum_intertwines ρ S hρ,orthogonalFusionTransport_sum,
    orthogonalFusionTransport_sum,← submoduleFamilySum_intertwines σ T hσ]
  congr 1
  funext i
  apply Subtype.ext
  exact he i z (x i)

end AMSPhysical
#print axioms AMSPhysical.orthogonalFusionTransport_intertwines
