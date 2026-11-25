import WeightedTranslation

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]

theorem weightedTranslation_naturality (e : X → Y) (s : X) (t : Y) (w : X → ℝ) (v : Y → ℝ)
    (he : ∀ x,e (x+s)=e x+t) (hw : ∀ x,v (e x)=w x) (f : X →₀ ℝ) :
    Finsupp.mapDomain e (weightedTranslation s w f)=
      weightedTranslation t v (Finsupp.mapDomain e f) := by
  have hMaps : (Finsupp.lmapDomain ℝ ℝ e).comp (weightedTranslation s w)=
      (weightedTranslation t v).comp (Finsupp.lmapDomain ℝ ℝ e) := by
    apply Finsupp.lhom_ext
    intro x a
    simp only [LinearMap.comp_apply,Finsupp.lmapDomain_apply,weightedTranslation_single,Finsupp.mapDomain_single,he,hw]
  exact DFunLike.congr_fun hMaps f

end AMSPhysical
