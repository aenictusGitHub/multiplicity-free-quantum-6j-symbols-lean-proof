import BilinearAdjoint
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3000000
noncomputable section
namespace AMSPhysical
variable {A V : Type*} [Ring A] [Algebra ℝ A] [AddCommGroup V] [Module ℝ V]

def algebraInvariant (ρ : A →ₐ[ℝ] Module.End ℝ V) (S : Submodule ℝ V) : Prop :=
  ∀ z : A,∀ v∈S,ρ z v∈S

def algebraCyclicSpan (ρ : A →ₐ[ℝ] Module.End ℝ V) (v : V) : Submodule ℝ V :=
  Submodule.span ℝ (Set.range (fun z : A => ρ z v))

theorem algebraCyclicSpan_self (ρ : A →ₐ[ℝ] Module.End ℝ V) (v : V) : v∈algebraCyclicSpan ρ v := by
  apply Submodule.subset_span
  exact ⟨1,by simp⟩

theorem algebraCyclicSpan_minimal (ρ : A →ₐ[ℝ] Module.End ℝ V) (v : V)
    (S : Submodule ℝ V) (hS : algebraInvariant ρ S) (hv : v∈S) : algebraCyclicSpan ρ v≤S := by
  apply Submodule.span_le.mpr
  rintro x ⟨z,rfl⟩
  exact hS z v hv

theorem algebraCyclicSpan_invariant (ρ : A →ₐ[ℝ] Module.End ℝ V) (v : V) :
    algebraInvariant ρ (algebraCyclicSpan ρ v) := by
  intro z w hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a,rfl⟩ := hx
    apply Submodule.subset_span
    exact ⟨z*a,by change ρ (z*a) v=ρ z (ρ a v);rw [map_mul];rfl⟩
  | zero => simpa only [map_zero] using (algebraCyclicSpan ρ v).zero_mem
  | add x y hx hy hix hiy => rw [map_add];exact (algebraCyclicSpan ρ v).add_mem hix hiy
  | smul c x hx hix => rw [map_smul];exact (algebraCyclicSpan ρ v).smul_mem c hix

theorem algebraInvariant_orthogonal (ρ : A →ₐ[ℝ] Module.End ℝ V)
    (B : LinearMap.BilinForm ℝ V) (hSym : ∀ v w,B v w=B w v)
    (hAdj : ∀ z : A,∃ u : A,PairAdjoint B (ρ z) (ρ u))
    (S : Submodule ℝ V) (hS : algebraInvariant ρ S) : algebraInvariant ρ (LinearMap.BilinForm.orthogonal B S) := by
  intro z w hw
  obtain ⟨u,hu⟩ := hAdj z
  intro s hs
  change B s (ρ z w)=0
  rw [hSym,hu w s,hSym]
  exact hw (ρ u s) (hS u s hs)

end AMSPhysical
#print axioms AMSPhysical.algebraInvariant_orthogonal
