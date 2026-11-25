import QuantumTypeALoweringSpan
import CompactTypeAPair
import BilinearCyclic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2800000
noncomputable section
namespace AMSPhysical
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Orthogonal highest vectors generate orthogonal full cyclic modules in
a genuine compact representation. Lowering spans and full algebra adjoints
are proved inputs, so this is not an assumed semisimple decomposition. -/
theorem compact_highest_cyclic_orthogonal (q : ℝ) (hq : q≠0) (n : ℕ)
    (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V) (B : LinearMap.BilinForm ℝ V)
    (hCompact : IsCompactTypeAPair q n B ρ) (hSym : ∀ x y,B x y=B y x)
    (v w : V) (lam mu : Fin n → ℤ)
    (hvE : ∀ i,ρ (typeAAlgebraGenerator q n i 0) v=0)
    (hwE : ∀ i,ρ (typeAAlgebraGenerator q n i 0) w=0)
    (hvK : ∀ i,ρ (typeAAlgebraGenerator q n i 2) v=q^(lam i) • v)
    (hwK : ∀ i,ρ (typeAAlgebraGenerator q n i 2) w=q^(mu i) • w)
    (hvw : B v w=0) :
    algebraCyclicSpan ρ w≤LinearMap.BilinForm.orthogonal B (algebraCyclicSpan ρ v) := by
  have hWords : ∀ u : List (Fin n),B (typeALoweredVector q n ρ v u) w=0 := by
    intro u
    cases u with
    | nil => simpa only [typeALoweredVector_nil] using hvw
    | cons i u =>
      rw [typeALoweredVector_cons,hCompact.adjF i]
      change B (typeALoweredVector q n ρ v u)
        (ρ (typeAAlgebraGenerator q n i 0) (ρ (typeAAlgebraGenerator q n i 3) w))=0
      rw [typeA_Ki_eigen_of_K q hq n ρ w i (mu i) (hwK i),map_smul,hwE,smul_zero,map_zero]
  have hLower : typeALoweringSpan q n ρ v≤LinearMap.ker (B.flip w) := by
    apply Submodule.span_le.mpr
    rintro z ⟨u,rfl⟩
    change B (typeALoweredVector q n ρ v u) w=0
    exact hWords u
  have hwO : w∈LinearMap.BilinForm.orthogonal B (algebraCyclicSpan ρ v) := by
    intro z hz
    apply hLower
    rw [typeALoweringSpan_eq_cyclic q hq n ρ v lam hvE hvK]
    exact hz
  exact algebraCyclicSpan_minimal ρ w _
    (algebraInvariant_orthogonal ρ B hSym hCompact.adjoint_exists
      (algebraCyclicSpan ρ v) (algebraCyclicSpan_invariant ρ v)) hwO

end AMSPhysical
