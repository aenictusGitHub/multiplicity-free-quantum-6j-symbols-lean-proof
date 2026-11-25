import PositiveFamilyEquiv
import QuantumHighestGram
import QuantumTypeALoweringSpan

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 4200000
noncomputable section
namespace AMSPhysical
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- An explicit isometric identification of equal-highest-weight cyclic
modules, constructed from their proved universal Gram coefficients. -/
def highestCyclicTransport (q : ℝ) (hq : q≠0) (n : ℕ)
    (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V) (σ : UqTypeA q n →ₐ[ℝ] Module.End ℝ W)
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (C : W →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (hB : IsCompactTypeAPair q n B ρ) (hC : IsCompactTypeAPair q n C σ)
    (hSymB : ∀ x y,B x y=B y x) (hSymC : ∀ x y,C x y=C y x)
    (hDefB : ∀ x,B x x=0 → x=0) (hDefC : ∀ x,C x x=0 → x=0)
    (v : V) (w : W) (lam : Fin n → ℤ)
    (hvE : ∀ i,ρ (typeAAlgebraGenerator q n i 0) v=0)
    (hwE : ∀ i,σ (typeAAlgebraGenerator q n i 0) w=0)
    (hvK : ∀ i,ρ (typeAAlgebraGenerator q n i 2) v=q^(lam i) • v)
    (hwK : ∀ i,σ (typeAAlgebraGenerator q n i 2) w=q^(lam i) • w)
    (hNorm : B v v=C w w) : algebraCyclicSpan ρ v ≃ₗ[ℝ] algebraCyclicSpan σ w :=
  ((LinearEquiv.ofEq _ _ (typeALoweringSpan_eq_cyclic q hq n ρ v lam hvE hvK)).symm.trans
    (positiveFamilyEquiv B C hDefB hDefC (typeALoweredVector q n ρ v) (typeALoweredVector q n σ w)
      (highest_lowering_Gram_unique q hq n ρ σ B C hB hC hSymB hSymC v w lam hvE hwE hvK hwK hNorm))).trans
    (LinearEquiv.ofEq _ _ (typeALoweringSpan_eq_cyclic q hq n σ w lam hwE hwK))


theorem loweringEvaluation_cyclic_mem (q : ℝ) (n : ℕ)
    (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V) (v : V) (f : List (Fin n) →₀ ℝ) :
    loweringEvaluation q n ρ v f∈algebraCyclicSpan ρ v := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add];exact (algebraCyclicSpan ρ v).add_mem hf hg
  | single u a =>
    rw [loweringEvaluation_single]
    exact (algebraCyclicSpan ρ v).smul_mem a (Submodule.subset_span ⟨typeALoweringWord q n u,rfl⟩)

section TransportProperties
variable (q : ℝ) (hq : q≠0) (n : ℕ)
    (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V) (σ : UqTypeA q n →ₐ[ℝ] Module.End ℝ W)
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (C : W →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (hB : IsCompactTypeAPair q n B ρ) (hC : IsCompactTypeAPair q n C σ)
    (hSymB : ∀ x y,B x y=B y x) (hSymC : ∀ x y,C x y=C y x)
    (hDefB : ∀ x,B x x=0 → x=0) (hDefC : ∀ x,C x x=0 → x=0)
    (v : V) (w : W) (lam : Fin n → ℤ)
    (hvE : ∀ i,ρ (typeAAlgebraGenerator q n i 0) v=0)
    (hwE : ∀ i,σ (typeAAlgebraGenerator q n i 0) w=0)
    (hvK : ∀ i,ρ (typeAAlgebraGenerator q n i 2) v=q^(lam i) • v)
    (hwK : ∀ i,σ (typeAAlgebraGenerator q n i 2) w=q^(lam i) • w)
    (hNorm : B v v=C w w)
local notation "T" => highestCyclicTransport q hq n ρ σ B C hB hC hSymB hSymC hDefB hDefC v w lam hvE hwE hvK hwK hNorm

theorem highestCyclicTransport_evaluation (f : List (Fin n) →₀ ℝ) :
    (T ⟨loweringEvaluation q n ρ v f,loweringEvaluation_cyclic_mem q n ρ v f⟩).val=
      loweringEvaluation q n σ w f := by
  unfold highestCyclicTransport
  simp only [LinearEquiv.trans_apply,LinearEquiv.ofEq_symm,LinearEquiv.coe_ofEq_apply]
  exact positiveFamilyEquiv_combination B C hDefB hDefC (typeALoweredVector q n ρ v)
    (typeALoweredVector q n σ w)
    (highest_lowering_Gram_unique q hq n ρ σ B C hB hC hSymB hSymC v w lam hvE hwE hvK hwK hNorm) f _

theorem highestCyclicTransport_isometry (x y : algebraCyclicSpan ρ v) :
    B x.val y.val=C (T x).val (T y).val := by
  unfold highestCyclicTransport
  simp only [LinearEquiv.trans_apply,LinearEquiv.ofEq_symm,LinearEquiv.coe_ofEq_apply]
  simpa only [LinearEquiv.coe_ofEq_apply] using positiveFamilyEquiv_isometry B C hDefB hDefC (typeALoweredVector q n ρ v)
    (typeALoweredVector q n σ w)
    (highest_lowering_Gram_unique q hq n ρ σ B C hB hC hSymB hSymC v w lam hvE hwE hvK hwK hNorm)
    (LinearEquiv.ofEq _ _ (typeALoweringSpan_eq_cyclic q hq n ρ v lam hvE hvK).symm x)
    (LinearEquiv.ofEq _ _ (typeALoweringSpan_eq_cyclic q hq n ρ v lam hvE hvK).symm y)
end TransportProperties

end AMSPhysical
#print axioms AMSPhysical.highestCyclicTransport
