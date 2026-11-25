import TriangularFamilyIndependent
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
noncomputable section
namespace AMSPhysical
variable {I V:Type*} [Fintype I] [DecidableEq I] [AddCommGroup V] [Module ℝ V]

def spanCoordinateMap (b:I → V) (coord:ℕ → V →ₗ[ℝ] ℝ):
    Submodule.span ℝ (Set.range b) →ₗ[ℝ] (ℕ → ℝ):=
  (LinearMap.pi coord).comp (Submodule.span ℝ (Set.range b)).subtype

/-- A triangular nonzero set of coordinates determines the entire span,
not merely independence of its named generators. -/
theorem triangular_spanCoordinateMap_injective (b:I → V) (index:I → ℕ)
    (hinj:Function.Injective index) (coord:ℕ → V →ₗ[ℝ] ℝ)
    (htri:∀ i y,y < index i → coord y (b i)=0)
    (hdiag:∀ i,coord (index i) (b i)≠0):Function.Injective (spanCoordinateMap b coord) := by
  have hi:=triangularFamily_linearIndependent b index hinj coord htri hdiag
  let B:Module.Basis I ℝ (Submodule.span ℝ (Set.range b)):=Module.Basis.span hi
  have hc:LinearIndependent ℝ (fun i:I=>fun y:ℕ=>coord y (b i)):=
    triangularFamily_linearIndependent (fun i:I=>fun y:ℕ=>coord y (b i)) index hinj
      (fun y=>LinearMap.proj y) htri hdiag
  refine LinearMap.injective_of_linearIndependent (R:=ℝ)
    (M:=Submodule.span ℝ (Set.range b)) (N:=ℕ → ℝ)
    (f:=spanCoordinateMap b coord) (v:=B) B.span_eq ?_
  change LinearIndependent ℝ (fun i:I=>fun y:ℕ=>coord y ((B i).val))
  simpa only [B,Module.Basis.span_apply] using hc

theorem triangular_span_ext (b:I → V) (index:I → ℕ)
    (hinj:Function.Injective index) (coord:ℕ → V →ₗ[ℝ] ℝ)
    (htri:∀ i y,y < index i → coord y (b i)=0)
    (hdiag:∀ i,coord (index i) (b i)≠0)
    (v w:V) (hv:v∈Submodule.span ℝ (Set.range b)) (hw:w∈Submodule.span ℝ (Set.range b))
    (hc:∀ y,coord y v=coord y w):v=w := by
  have he:spanCoordinateMap b coord ⟨v,hv⟩=spanCoordinateMap b coord ⟨w,hw⟩:=by
    funext y
    exact hc y
  exact congrArg Subtype.val ((triangular_spanCoordinateMap_injective b index hinj coord htri hdiag) he)

end AMSPhysical
#print axioms AMSPhysical.triangular_span_ext
