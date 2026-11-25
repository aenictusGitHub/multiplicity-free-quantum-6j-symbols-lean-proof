import QuantumTypeAWordRaising

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3600000
noncomputable section
namespace AMSPhysical
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def loweringEvaluation (q : ℝ) (n : ℕ) (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V) (v : V) :
    (List (Fin n) →₀ ℝ) →ₗ[ℝ] V := Finsupp.linearCombination ℝ (typeALoweredVector q n ρ v)

@[simp] theorem loweringEvaluation_single (q : ℝ) (n : ℕ) (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V)
    (v : V) (w : List (Fin n)) (a : ℝ) :
    loweringEvaluation q n ρ v (Finsupp.single w a)=a • typeALoweredVector q n ρ v w := by
  simp [loweringEvaluation]

theorem loweringEvaluation_prefix (q : ℝ) (n : ℕ) (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V)
    (v : V) (j : Fin n) (f : List (Fin n) →₀ ℝ) :
    loweringEvaluation q n ρ v (Finsupp.mapDomain (List.cons j) f)=
      ρ (typeAAlgebraGenerator q n j 1) (loweringEvaluation q n ρ v f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [Finsupp.mapDomain_add,map_add,hf,hg]
  | single w a => simp [typeALoweredVector_cons]

/-- A universal, finite expansion of E_i applied to any lowering word. -/
def raisingWordExpansion (q : ℝ) (n : ℕ) (lam : Fin n → ℤ) (i : Fin n) :
    List (Fin n) → (List (Fin n) →₀ ℝ)
  | [] => 0
  | j::w => Finsupp.mapDomain (List.cons j) (raisingWordExpansion q n lam i w)+
      Finsupp.single w (if i=j then qInteger q (loweringWordWeight n lam w i) else 0)

theorem typeALoweredVector_E_expansion (q : ℝ) (hq : q≠0) (n : ℕ)
    (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V) (v : V) (lam : Fin n → ℤ)
    (hvE : ∀ i,ρ (typeAAlgebraGenerator q n i 0) v=0)
    (hvK : ∀ i,ρ (typeAAlgebraGenerator q n i 2) v=q^(lam i) • v)
    (i : Fin n) (w : List (Fin n)) :
    ρ (typeAAlgebraGenerator q n i 0) (typeALoweredVector q n ρ v w)=
      loweringEvaluation q n ρ v (raisingWordExpansion q n lam i w) := by
  induction w with
  | nil => simpa only [typeALoweredVector_nil,raisingWordExpansion,map_zero] using hvE i
  | cons j w ih =>
    rw [typeALoweredVector_E_cons q hq n ρ v lam hvK i j w,raisingWordExpansion,map_add,
      loweringEvaluation_prefix,loweringEvaluation_single,← ih]

end AMSPhysical
#print axioms AMSPhysical.typeALoweredVector_E_expansion
