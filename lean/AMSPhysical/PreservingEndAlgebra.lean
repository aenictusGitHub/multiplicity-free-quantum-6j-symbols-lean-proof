import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Basic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
noncomputable section
namespace AMSPhysical

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def preservingEndAlgebra (S : Submodule K V) : Subalgebra K (Module.End K V) where
  carrier := {T | ∀ x∈S,T x∈S}
  zero_mem' := by intro x hx;simpa only [LinearMap.zero_apply] using S.zero_mem
  one_mem' := by intro x hx;exact hx
  add_mem' := by intro T U hT hU x hx;exact S.add_mem (hT x hx) (hU x hx)
  mul_mem' := by intro T U hT hU x hx;exact hT (U x) (hU x hx)
  algebraMap_mem' := by intro c x hx;change c • x∈S;exact S.smul_mem c hx

def restrictPreservingEnd (S : Submodule K V) : preservingEndAlgebra S →ₐ[K] Module.End K S where
  toFun T :=
    { toFun := fun x => ⟨T.val x.val,T.property x.val x.property⟩
      map_add' := by intro x y;apply Subtype.ext;exact T.val.map_add x.val y.val
      map_smul' := by intro c x;apply Subtype.ext;exact T.val.map_smul c x.val }
  map_one' := by ext x; rfl
  map_mul' := by intro T U;ext x;rfl
  map_zero' := by ext x;rfl
  map_add' := by intro T U;ext x;rfl
  commutes' := by intro c;ext x;rfl

@[simp] theorem restrictPreservingEnd_apply (S : Submodule K V) (T : preservingEndAlgebra S) (x : S) :
    (restrictPreservingEnd S T x).val=T.val x.val := rfl

end AMSPhysical

#print axioms AMSPhysical.restrictPreservingEnd
