import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
noncomputable section
namespace AMSPhysical
open Module Polynomial
variable {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype I] [LinearOrder I] [FiniteDimensional K V]

theorem lowerTriangular_charpoly (b : Basis I K V) (A : Module.End K V)
    (hA : ∀ i j,i<j → b.repr (A (b j)) i=0) :
    A.charpoly=∏ i : I,(X-C (b.repr (A (b i)) i)) := by
  rw [← LinearMap.charpoly_toMatrix A b,← Matrix.charpoly_transpose]
  have ht : ((LinearMap.toMatrix b b) A).transpose.BlockTriangular id := by
    intro i j hij
    simp only [Matrix.transpose_apply,LinearMap.toMatrix_apply]
    change b.repr (A (b i)) j=0
    exact hA j i hij
  simpa only [Matrix.transpose_apply,LinearMap.toMatrix_apply] using
    Matrix.charpoly_of_upperTriangular ((LinearMap.toMatrix b b) A).transpose ht

theorem distinct_linear_factors_rootMultiplicity (lam : I → K) (hinj : Function.Injective lam) (i : I) :
    (∏ j : I,(X-C (lam j))).rootMultiplicity (lam i)=1 := by
  classical
  have he : (∏ j : I,(X-C (lam j)))=∏ a∈Finset.image lam Finset.univ,(X-C a) := by
    symm
    apply Finset.prod_image
    intro a b _ _ h
    exact hinj h
  rw [he,← Polynomial.count_roots,Polynomial.roots_prod_X_sub_C]
  exact Multiset.count_eq_one_of_mem (Finset.nodup _) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)

theorem lowerTriangular_eigenspace_finrank (b : Basis I K V) (A : Module.End K V)
    (lam : I → K) (hinj : Function.Injective lam)
    (hA : ∀ i j,i<j → b.repr (A (b j)) i=0)
    (hdiag : ∀ i,b.repr (A (b i)) i=lam i) (i : I) :
    Module.finrank K (A.eigenspace (lam i))=1 := by
  have hchar : A.charpoly=∏ j : I,(X-C (lam j)) := by
    rw [lowerTriangular_charpoly b A hA]
    simp only [hdiag]
  have hroot : A.charpoly.IsRoot (lam i) := by
    rw [hchar,Polynomial.IsRoot,Polynomial.eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp
  have hnonzero : A.eigenspace (lam i)≠⊥ :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly A (lam i)).mpr hroot
  haveI : Nontrivial (A.eigenspace (lam i)) := Submodule.nontrivial_iff_ne_bot.mpr hnonzero
  have hlo : 0<Module.finrank K (A.eigenspace (lam i)) := Module.finrank_pos
  have hhi:=LinearMap.finrank_eigenspace_le A (lam i)
  rw [hchar,distinct_linear_factors_rootMultiplicity lam hinj i] at hhi
  omega

theorem upperTriangular_eigenspace_finrank (b : Basis I K V) (A : Module.End K V)
    (lam : I → K) (hinj : Function.Injective lam)
    (hA : ∀ i j,j < i → b.repr (A (b j)) i=0)
    (hdiag : ∀ i,b.repr (A (b i)) i=lam i) (i : I) :
    Module.finrank K (A.eigenspace (lam i))=1 := by
  exact lowerTriangular_eigenspace_finrank (I:=OrderDual I) b A lam hinj hA hdiag i

end AMSPhysical
#print axioms AMSPhysical.lowerTriangular_eigenspace_finrank
