import QuantumTypeALoweringSpan
import QuantumWordEvaluation

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 4200000
noncomputable section
namespace AMSPhysical
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

def pairedLoweringSpan (q : ℝ) (n : ℕ)
    (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V) (σ : UqTypeA q n →ₐ[ℝ] Module.End ℝ W) (v : V) (w : W) :
    Submodule ℝ (V×W) :=
  Submodule.span ℝ (Set.range (fun u : List (Fin n) => (typeALoweredVector q n ρ v u,typeALoweredVector q n σ w u)))

theorem pairedLowering_combination (q : ℝ) (n : ℕ)
    (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V) (σ : UqTypeA q n →ₐ[ℝ] Module.End ℝ W)
    (v : V) (w : W) (f : List (Fin n) →₀ ℝ) :
    Finsupp.linearCombination ℝ (fun u : List (Fin n) =>
      (typeALoweredVector q n ρ v u,typeALoweredVector q n σ w u)) f=
      (loweringEvaluation q n ρ v f,loweringEvaluation q n σ w f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero];rfl
  | add f g hf hg => simp only [map_add,hf,hg];rfl
  | single u a => simp only [Finsupp.linearCombination_single,loweringEvaluation_single];rfl

theorem pairedLowering_eval_mem (q : ℝ) (n : ℕ)
    (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V) (σ : UqTypeA q n →ₐ[ℝ] Module.End ℝ W)
    (v : V) (w : W) (f : List (Fin n) →₀ ℝ) :
    (loweringEvaluation q n ρ v f,loweringEvaluation q n σ w f)∈pairedLoweringSpan q n ρ σ v w := by
  rw [← pairedLowering_combination]
  change Finsupp.linearCombination ℝ _ f∈Submodule.span ℝ _
  rw [← Finsupp.range_linearCombination]
  exact ⟨f,rfl⟩

theorem pairedLowering_common_combination (q : ℝ) (n : ℕ)
    (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V) (σ : UqTypeA q n →ₐ[ℝ] Module.End ℝ W)
    (v : V) (w : W) (x : V) (y : W) (hxy : (x,y)∈pairedLoweringSpan q n ρ σ v w) :
    ∃ f : List (Fin n) →₀ ℝ,loweringEvaluation q n ρ v f=x ∧ loweringEvaluation q n σ w f=y := by
  change (x,y)∈Submodule.span ℝ _ at hxy
  rw [← Finsupp.range_linearCombination] at hxy
  obtain ⟨f,hf⟩ := hxy
  rw [pairedLowering_combination] at hf
  exact ⟨f,congrArg Prod.fst hf,congrArg Prod.snd hf⟩

end AMSPhysical
#print axioms AMSPhysical.pairedLowering_common_combination
