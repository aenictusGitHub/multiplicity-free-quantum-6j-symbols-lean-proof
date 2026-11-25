import BilinearOrthonormal
import Mathlib.LinearAlgebra.Basis.Defs

set_option autoImplicit false
noncomputable section
namespace AMSPhysical
variable {I V W:Type*} [DecidableEq I] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]

/-- The equivalence matching actual orthonormal bases is an exact isometry. -/
theorem bilinearBasisEquiv_isometry (B:LinearMap.BilinForm ℝ V) (C:LinearMap.BilinForm ℝ W)
    (b:Module.Basis I ℝ V) (c:Module.Basis I ℝ W)
    (hb:∀ i j,B (b i) (b j)=if i=j then 1 else 0)
    (hc:∀ i j,C (c i) (c j)=if i=j then 1 else 0) (v w:V):
    C (b.equiv c (Equiv.refl I) v) (b.equiv c (Equiv.refl I) w)=B v w := by
  have he:C.compl₁₂ (b.equiv c (Equiv.refl I)).toLinearMap
      (b.equiv c (Equiv.refl I)).toLinearMap=B:=by
    apply b.ext
    intro i
    apply b.ext
    intro j
    change C (b.equiv c (Equiv.refl I) (b i)) (b.equiv c (Equiv.refl I) (b j))=_
    rw [Module.Basis.equiv_apply,Module.Basis.equiv_apply,hb,hc]
    rfl
  exact DFunLike.congr_fun (DFunLike.congr_fun he v) w

end AMSPhysical
#print axioms AMSPhysical.bilinearBasisEquiv_isometry
