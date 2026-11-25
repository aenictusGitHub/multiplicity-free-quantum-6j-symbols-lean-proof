import QuantumWordEvaluation
import CompactTypeAPair

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 4200000
noncomputable section
namespace AMSPhysical
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

theorem loweringGram_step (q : ℝ) (hq : q≠0) (n : ℕ)
    (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hB : IsCompactTypeAPair q n B ρ) (v : V) (lam : Fin n → ℤ)
    (hvE : ∀ i,ρ (typeAAlgebraGenerator q n i 0) v=0)
    (hvK : ∀ i,ρ (typeAAlgebraGenerator q n i 2) v=q^(lam i) • v)
    (i : Fin n) (u w : List (Fin n)) :
    B (typeALoweredVector q n ρ v (i::u)) (typeALoweredVector q n ρ v w)=
      q^(-loweringWordWeight n lam w i)*
        (raisingWordExpansion q n lam i w).sum
          (fun t a => a*B (typeALoweredVector q n ρ v u) (typeALoweredVector q n ρ v t)) := by
  rw [typeALoweredVector_cons,hB.adjF i,Module.End.mul_apply,
    typeALoweredVector_Ki q hq n ρ v lam hvK w i,map_smul,map_smul,smul_eq_mul,
    typeALoweredVector_E_expansion q hq n ρ v lam hvE hvK i w]
  unfold loweringEvaluation
  rw [Finsupp.linearCombination_apply]
  simp only [Finsupp.sum,map_sum,map_smul,smul_eq_mul]

/-- All Gram coefficients of normalized highest modules depend only on their
highest weight. The universal raising recursion is a proved conclusion. -/
theorem highest_lowering_Gram_unique (q : ℝ) (hq : q≠0) (n : ℕ)
    (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V) (σ : UqTypeA q n →ₐ[ℝ] Module.End ℝ W)
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (C : W →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (hB : IsCompactTypeAPair q n B ρ) (hC : IsCompactTypeAPair q n C σ)
    (hSymB : ∀ x y,B x y=B y x) (hSymC : ∀ x y,C x y=C y x)
    (v : V) (w : W) (lam : Fin n → ℤ)
    (hvE : ∀ i,ρ (typeAAlgebraGenerator q n i 0) v=0)
    (hwE : ∀ i,σ (typeAAlgebraGenerator q n i 0) w=0)
    (hvK : ∀ i,ρ (typeAAlgebraGenerator q n i 2) v=q^(lam i) • v)
    (hwK : ∀ i,σ (typeAAlgebraGenerator q n i 2) w=q^(lam i) • w)
    (hNorm : B v v=C w w) :
    ∀ u t : List (Fin n),B (typeALoweredVector q n ρ v u) (typeALoweredVector q n ρ v t)=
      C (typeALoweredVector q n σ w u) (typeALoweredVector q n σ w t) := by
  intro u
  induction u with
  | nil =>
    intro t
    cases t with
    | nil => simpa only [typeALoweredVector_nil] using hNorm
    | cons i t =>
      simp only [typeALoweredVector_nil,typeALoweredVector_cons]
      rw [hSymB v,hSymC w,hB.adjF i,hC.adjF i,Module.End.mul_apply,Module.End.mul_apply,
        typeA_Ki_eigen_of_K q hq n ρ v i (lam i) (hvK i),
        typeA_Ki_eigen_of_K q hq n σ w i (lam i) (hwK i)]
      simp only [map_smul,hvE,hwE,smul_zero,map_zero]
  | cons i u ih =>
    intro t
    rw [loweringGram_step q hq n ρ B hB v lam hvE hvK i u t,
      loweringGram_step q hq n σ C hC w lam hwE hwK i u t]
    congr 1
    apply Finset.sum_congr rfl
    intro z hz
    dsimp only
    rw [ih z]

end AMSPhysical
#print axioms AMSPhysical.highest_lowering_Gram_unique
