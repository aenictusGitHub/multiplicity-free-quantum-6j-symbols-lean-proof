import PairedLoweringSpan

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 4200000
noncomputable section
namespace AMSPhysical
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- Equal-highest-weight lowering relations are preserved by EVERY element
of the full quantum algebra, proved directly from the generator actions. -/
theorem pairedLoweringSpan_invariant (q : ℝ) (hq : q≠0) (n : ℕ)
    (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V) (σ : UqTypeA q n →ₐ[ℝ] Module.End ℝ W)
    (v : V) (w : W) (lam : Fin n → ℤ)
    (hvE : ∀ i,ρ (typeAAlgebraGenerator q n i 0) v=0)
    (hwE : ∀ i,σ (typeAAlgebraGenerator q n i 0) w=0)
    (hvK : ∀ i,ρ (typeAAlgebraGenerator q n i 2) v=q^(lam i) • v)
    (hwK : ∀ i,σ (typeAAlgebraGenerator q n i 2) w=q^(lam i) • w) :
    ∀ z : UqTypeA q n,∀ x y,(x,y)∈pairedLoweringSpan q n ρ σ v w →
      (ρ z x,σ z y)∈pairedLoweringSpan q n ρ σ v w := by
  let S := pairedLoweringSpan q n ρ σ v w
  have hgen : ∀ (i : Fin n) (t : Fin 4),
      LinearMap.prodMap (ρ (typeAAlgebraGenerator q n i t)) (σ (typeAAlgebraGenerator q n i t))∈preservingEndAlgebra S := by
    intro i t
    fin_cases t
    · change LinearMap.prodMap (ρ (typeAAlgebraGenerator q n i 0)) (σ (typeAAlgebraGenerator q n i 0))∈preservingEndAlgebra S
      apply span_preserving_of_family
      intro u
      change (ρ (typeAAlgebraGenerator q n i 0) (typeALoweredVector q n ρ v u),
        σ (typeAAlgebraGenerator q n i 0) (typeALoweredVector q n σ w u))∈S
      rw [typeALoweredVector_E_expansion q hq n ρ v lam hvE hvK,
        typeALoweredVector_E_expansion q hq n σ w lam hwE hwK]
      exact pairedLowering_eval_mem q n ρ σ v w _
    · change LinearMap.prodMap (ρ (typeAAlgebraGenerator q n i 1)) (σ (typeAAlgebraGenerator q n i 1))∈preservingEndAlgebra S
      apply span_preserving_of_family
      intro u
      change (ρ (typeAAlgebraGenerator q n i 1) (typeALoweredVector q n ρ v u),
        σ (typeAAlgebraGenerator q n i 1) (typeALoweredVector q n σ w u))∈S
      rw [← typeALoweredVector_cons,← typeALoweredVector_cons]
      exact Submodule.subset_span ⟨i::u,rfl⟩
    · change LinearMap.prodMap (ρ (typeAAlgebraGenerator q n i 2)) (σ (typeAAlgebraGenerator q n i 2))∈preservingEndAlgebra S
      apply span_preserving_of_family
      intro u
      change (ρ (typeAAlgebraGenerator q n i 2) (typeALoweredVector q n ρ v u),
        σ (typeAAlgebraGenerator q n i 2) (typeALoweredVector q n σ w u))∈S
      rw [typeALoweredVector_K q hq n ρ v lam hvK,typeALoweredVector_K q hq n σ w lam hwK]
      exact S.smul_mem _ (Submodule.subset_span ⟨u,rfl⟩)
    · change LinearMap.prodMap (ρ (typeAAlgebraGenerator q n i 3)) (σ (typeAAlgebraGenerator q n i 3))∈preservingEndAlgebra S
      apply span_preserving_of_family
      intro u
      change (ρ (typeAAlgebraGenerator q n i 3) (typeALoweredVector q n ρ v u),
        σ (typeAAlgebraGenerator q n i 3) (typeALoweredVector q n σ w u))∈S
      rw [typeALoweredVector_Ki q hq n ρ v lam hvK,typeALoweredVector_Ki q hq n σ w lam hwK]
      exact S.smul_mem _ (Submodule.subset_span ⟨u,rfl⟩)
  intro z
  obtain ⟨a,rfl⟩ := RingQuot.mkAlgHom_surjective ℝ (QuantumTypeARelation q n) z
  induction a using FreeAlgebra.induction with
  | grade0 c =>
    intro x y hxy
    simpa [Algebra.algebraMap_eq_smul_one] using S.smul_mem c hxy
  | grade1 it =>
    intro x y hxy
    exact hgen it.1 it.2 (x,y) hxy
  | mul a b ha hb =>
    intro x y hxy
    simpa only [map_mul,Module.End.mul_apply] using ha _ _ (hb x y hxy)
  | add a b ha hb =>
    intro x y hxy
    simpa only [map_add,LinearMap.add_apply] using S.add_mem (ha x y hxy) (hb x y hxy)

end AMSPhysical
#print axioms AMSPhysical.pairedLoweringSpan_invariant
