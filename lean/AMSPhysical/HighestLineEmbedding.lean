import NativeInnerHighestLines

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

theorem finrank_one_of_line_embedding (S : Submodule ℝ W) (hS : Module.finrank ℝ S=1)
    (F : V →ₗ[ℝ] W) (hF : Function.Injective F) (hRange : ∀ v,F v∈S)
    (v : V) (hv : v≠0) : Module.finrank ℝ V=1 := by
  let G : V →ₗ[ℝ] S:=F.codRestrict S hRange
  have hG : Function.Injective G := by intro x y he;exact hF (congrArg Subtype.val he)
  have hV : G v≠0 := by intro he;exact hv (hG (by simpa only [map_zero] using he))
  have hSurj : Function.Surjective G := by
    intro w
    obtain ⟨a,ha⟩:=exists_smul_eq_of_finrank_eq_one hS hV w
    exact ⟨a • v,by rw [map_smul,ha]⟩
  exact (LinearEquiv.ofBijective G ⟨hG,hSurj⟩).finrank_eq.trans hS

end AMSPhysical
#print axioms AMSPhysical.finrank_one_of_line_embedding
