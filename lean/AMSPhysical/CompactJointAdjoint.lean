import CompactTypeAPair

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- The SAME algebra element represents the adjoint simultaneously in two
independently constructed compact representations. -/
theorem IsCompactTypeAPair.joint_adjoint_exists {q : ℝ} {n : ℕ}
    {B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {C : W →ₗ[ℝ] W →ₗ[ℝ] ℝ}
    {ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V} {σ : UqTypeA q n →ₐ[ℝ] Module.End ℝ W}
    (h : IsCompactTypeAPair q n B ρ) (g : IsCompactTypeAPair q n C σ) (z : UqTypeA q n) :
    ∃ u : UqTypeA q n,PairAdjoint B (ρ z) (ρ u) ∧ PairAdjoint C (σ z) (σ u) := by
  obtain ⟨a,rfl⟩ := RingQuot.mkAlgHom_surjective ℝ (QuantumTypeARelation q n) z
  induction a using FreeAlgebra.induction with
  | grade0 c =>
    refine ⟨algebraMap ℝ (UqTypeA q n) c,?_,?_⟩
    · simpa [Algebra.algebraMap_eq_smul_one] using (PairAdjoint.id B).smul c
    · simpa [Algebra.algebraMap_eq_smul_one] using (PairAdjoint.id C).smul c
  | grade1 it =>
    obtain ⟨i,t⟩ := it
    change ∃ u,PairAdjoint B (ρ (typeAAlgebraGenerator q n i t)) (ρ u) ∧
      PairAdjoint C (σ (typeAAlgebraGenerator q n i t)) (σ u)
    fin_cases t
    · exact ⟨typeAAlgebraGenerator q n i 2*typeAAlgebraGenerator q n i 1,
        by simpa only [map_mul] using h.adjE i,by simpa only [map_mul] using g.adjE i⟩
    · exact ⟨typeAAlgebraGenerator q n i 0*typeAAlgebraGenerator q n i 3,
        by simpa only [map_mul] using h.adjF i,by simpa only [map_mul] using g.adjF i⟩
    · exact ⟨typeAAlgebraGenerator q n i 2,h.adjK i,g.adjK i⟩
    · exact ⟨typeAAlgebraGenerator q n i 3,h.adjKi i,g.adjKi i⟩
  | mul a b ha hb =>
    obtain ⟨u,hu,gu⟩ := ha
    obtain ⟨v,hv,gv⟩ := hb
    exact ⟨v*u,by simpa only [map_mul] using hu.mul hv,by simpa only [map_mul] using gu.mul gv⟩
  | add a b ha hb =>
    obtain ⟨u,hu,gu⟩ := ha
    obtain ⟨v,hv,gv⟩ := hb
    exact ⟨u+v,by simpa only [map_add] using hu.add hv,by simpa only [map_add] using gu.add gv⟩

/-- The actual metric adjoint of an intertwiner again intertwines. The
conclusion uses the proved common algebraic adjoint, not an extra star axiom. -/
theorem compact_intertwiner_adjoint {q : ℝ} {n : ℕ}
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (C : W →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V) (σ : UqTypeA q n →ₐ[ℝ] Module.End ℝ W)
    (h : IsCompactTypeAPair q n B ρ) (g : IsCompactTypeAPair q n C σ)
    (hB : Function.Injective B) (hSymB : ∀ v w,B v w=B w v) (hSymC : ∀ v w,C v w=C w v)
    (T : V →ₗ[ℝ] W) (D : W →ₗ[ℝ] V)
    (hT : ∀ z v,T (ρ z v)=σ z (T v)) (hD : ∀ v w,C (T v) w=B v (D w))
    (z : UqTypeA q n) (w : W) : D (σ z w)=ρ z (D w) := by
  apply hB
  apply LinearMap.ext
  intro v
  obtain ⟨u,hu,gu⟩ := h.joint_adjoint_exists g z
  calc
    B (D (σ z w)) v = B v (D (σ z w)) := hSymB _ _
    _ = C (T v) (σ z w) := (hD _ _).symm
    _ = C (σ z w) (T v) := hSymC _ _
    _ = C w (σ u (T v)) := gu _ _
    _ = C w (T (ρ u v)) := congrArg (C w) (hT u v).symm
    _ = C (T (ρ u v)) w := hSymC _ _
    _ = B (ρ u v) (D w) := hD _ _
    _ = B (D w) (ρ u v) := hSymB _ _
    _ = B (ρ z (D w)) v := (hu _ _).symm

end AMSPhysical
