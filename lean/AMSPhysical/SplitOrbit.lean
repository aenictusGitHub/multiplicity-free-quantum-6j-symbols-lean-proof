import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
noncomputable section
namespace AMSPhysical

variable {K U V : Type*} [Field K]
  [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]

/-- A surjection with a specified section splits into its image coordinates
and its actual kernel. -/
def sectionSplit (X : U →ₗ[K] V) (Y : V →ₗ[K] U) (hYX : ∀ u,Y (X u)=u) :
    V ≃ₗ[K] U×(LinearMap.ker Y) where
  toFun v := (Y v,⟨v-X (Y v),by simp [LinearMap.mem_ker,hYX]⟩)
  invFun p := X p.1+p.2
  left_inv v := by simp
  right_inv p := by
    obtain ⟨u,k⟩ := p
    have hk : Y (k:V)=0 := k.property
    apply Prod.ext
    · simp [hYX,hk]
    · apply Subtype.ext
      simp [hYX,hk]
  map_add' v w := by
    apply Prod.ext
    · simp
    · apply Subtype.ext
      simp only [map_add,Submodule.coe_add]
      dsimp
      module
  map_smul' c v := by
    apply Prod.ext
    · simp
    · apply Subtype.ext
      simp only [map_smul,Submodule.coe_smul]
      dsimp
      module

theorem sectionSplit_fst (X : U →ₗ[K] V) (Y : V →ₗ[K] U) (hYX : ∀ u,Y (X u)=u)
    (v : V) : (sectionSplit X Y hYX v).1=Y v := rfl

theorem sectionSplit_section (X : U →ₗ[K] V) (Y : V →ₗ[K] U) (hYX : ∀ u,Y (X u)=u)
    (u : U) : sectionSplit X Y hYX (X u)=(u,0) := by
  apply Prod.ext
  · exact hYX u
  · apply Subtype.ext
    simp [sectionSplit,hYX]

/-- Two split frames with dual coordinates lie in the same genuine GL(V) orbit. -/
theorem split_frame_orbit [FiniteDimensional K U] [FiniteDimensional K V]
    (X X₀ : U →ₗ[K] V) (Y Y₀ : V →ₗ[K] U)
    (hYX : ∀ u,Y (X u)=u) (hY₀X₀ : ∀ u,Y₀ (X₀ u)=u) :
    ∃ g : V ≃ₗ[K] V, (∀ u,g (X u)=X₀ u) ∧ (∀ v,Y₀ (g v)=Y v) := by
  have hY : Function.Surjective Y := fun u => ⟨X u,hYX u⟩
  have hY₀ : Function.Surjective Y₀ := fun u => ⟨X₀ u,hY₀X₀ u⟩
  have hd : Module.finrank K (LinearMap.ker Y)=Module.finrank K (LinearMap.ker Y₀) := by
    have h₁ := LinearMap.finrank_range_add_finrank_ker Y
    have h₂ := LinearMap.finrank_range_add_finrank_ker Y₀
    rw [LinearMap.range_eq_top.mpr hY,finrank_top] at h₁
    rw [LinearMap.range_eq_top.mpr hY₀,finrank_top] at h₂
    omega
  let e := sectionSplit X Y hYX
  let e₀ := sectionSplit X₀ Y₀ hY₀X₀
  let k := LinearEquiv.ofFinrankEq (LinearMap.ker Y) (LinearMap.ker Y₀) hd
  let g := e.trans ((LinearEquiv.refl K U).prodCongr k) |>.trans e₀.symm
  refine ⟨g,?_,?_⟩
  · intro u
    have he : e (X u)=(u,0) := sectionSplit_section X Y hYX u
    have he₀ : e₀ (X₀ u)=(u,0) := sectionSplit_section X₀ Y₀ hY₀X₀ u
    apply e₀.injective
    simp [g,he,he₀]
  · intro v
    have he : e₀ (g v)=((LinearEquiv.refl K U).prodCongr k) (e v) := by simp [g]
    have hh := congrArg Prod.fst he
    simpa [e,e₀,sectionSplit] using hh

theorem nondegenerate_frame_orbit [FiniteDimensional K U] [FiniteDimensional K V]
    (X X₀ : U →ₗ[K] V) (Y Y₀ : V →ₗ[K] U) (Z : U ≃ₗ[K] U)
    (hYX : ∀ u,Y (X u)=Z u) (hY₀X₀ : ∀ u,Y₀ (X₀ u)=u) :
    ∃ g : V ≃ₗ[K] V, (∀ u,g (X u)=X₀ (Z u)) ∧ (∀ v,Y₀ (g v)=Y v) := by
  let Xs := X.comp Z.symm.toLinearMap
  have hsec : ∀ u,Y (Xs u)=u := by intro u; simp [Xs,hYX]
  obtain ⟨g,hg,hY⟩ := split_frame_orbit Xs X₀ Y Y₀ hsec hY₀X₀
  refine ⟨g,?_,hY⟩
  intro u
  have he := hg (Z u)
  simpa [Xs] using he

end AMSPhysical

#print axioms AMSPhysical.split_frame_orbit
