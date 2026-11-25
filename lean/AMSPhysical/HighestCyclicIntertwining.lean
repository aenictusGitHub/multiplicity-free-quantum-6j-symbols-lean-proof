import HighestCyclicTransport
import PairedLoweringInvariant
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 4200000
noncomputable section
namespace AMSPhysical
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
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


theorem highestCyclicTransport_graph (x : algebraCyclicSpan ρ v) :
    (x.val,(T x).val)∈pairedLoweringSpan q n ρ σ v w := by
  have hxR : x.val∈LinearMap.range (loweringEvaluation q n ρ v) := by
    change x.val∈LinearMap.range (Finsupp.linearCombination ℝ (typeALoweredVector q n ρ v))
    rw [Finsupp.range_linearCombination]
    change x.val∈typeALoweringSpan q n ρ v
    rw [typeALoweringSpan_eq_cyclic q hq n ρ v lam hvE hvK]
    exact x.property
  obtain ⟨f,hf⟩ := hxR
  have hx : x=⟨loweringEvaluation q n ρ v f,loweringEvaluation_cyclic_mem q n ρ v f⟩ := Subtype.ext hf.symm
  rw [hx,highestCyclicTransport_evaluation]
  exact pairedLowering_eval_mem q n ρ σ v w f

/-- The canonical positive highest-module transport intertwines EVERY actual
algebra element, not just the lowering generators or the Cartan torus. -/
theorem highestCyclicTransport_intertwines (z : UqTypeA q n) (x : algebraCyclicSpan ρ v) :
    (T ⟨ρ z x.val,algebraCyclicSpan_invariant ρ v z x.val x.property⟩).val=σ z (T x).val := by
  have hg := highestCyclicTransport_graph q hq n ρ σ B C hB hC hSymB hSymC hDefB hDefC v w lam hvE hwE hvK hwK hNorm x
  have hz := pairedLoweringSpan_invariant q hq n ρ σ v w lam hvE hwE hvK hwK z _ _ hg
  obtain ⟨f,hf,hf'⟩ := pairedLowering_common_combination q n ρ σ v w _ _ hz
  have hx : (⟨ρ z x.val,algebraCyclicSpan_invariant ρ v z x.val x.property⟩ : algebraCyclicSpan ρ v)=
      ⟨loweringEvaluation q n ρ v f,loweringEvaluation_cyclic_mem q n ρ v f⟩ := Subtype.ext hf.symm
  rw [hx,highestCyclicTransport_evaluation]
  exact hf'


theorem highestCyclicTransport_highest :
    (T ⟨v,algebraCyclicSpan_self ρ v⟩).val=w := by
  have he := highestCyclicTransport_evaluation q hq n ρ σ B C hB hC hSymB hSymC hDefB hDefC v w lam hvE hwE hvK hwK hNorm (Finsupp.single [] 1)
  simpa only [loweringEvaluation_single,typeALoweredVector_nil,one_smul] using he

end TransportProperties
end AMSPhysical
#print axioms AMSPhysical.highestCyclicTransport_intertwines
