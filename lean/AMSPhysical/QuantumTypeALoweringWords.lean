import QuantumTypeAInverseWeights

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3000000
noncomputable section
namespace AMSPhysical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def typeALoweringWord (q : K) (n : ℕ) (w : List (Fin n)) : UqTypeA q n :=
  (w.map (fun j => typeAAlgebraGenerator q n j 1)).prod

def typeALoweredVector (q : K) (n : ℕ) (ρ : UqTypeA q n →ₐ[K] Module.End K V)
    (v : V) (w : List (Fin n)) : V := ρ (typeALoweringWord q n w) v

def loweringWordWeight (n : ℕ) (lam : Fin n → ℤ) (w : List (Fin n)) (i : Fin n) : ℤ :=
  lam i-(w.map (fun j => typeACartan n i j)).sum

@[simp] theorem typeALoweringWord_nil (q : K) (n : ℕ) : typeALoweringWord q n []=1 := rfl
@[simp] theorem typeALoweringWord_cons (q : K) (n : ℕ) (j : Fin n) (w : List (Fin n)) :
    typeALoweringWord q n (j::w)=typeAAlgebraGenerator q n j 1*typeALoweringWord q n w := rfl
@[simp] theorem typeALoweredVector_nil (q : K) (n : ℕ) (ρ : UqTypeA q n →ₐ[K] Module.End K V) (v : V) :
    typeALoweredVector q n ρ v []=v := by simp [typeALoweredVector]
@[simp] theorem typeALoweredVector_cons (q : K) (n : ℕ) (ρ : UqTypeA q n →ₐ[K] Module.End K V)
    (v : V) (j : Fin n) (w : List (Fin n)) :
    typeALoweredVector q n ρ v (j::w)=ρ (typeAAlgebraGenerator q n j 1) (typeALoweredVector q n ρ v w) := by
  simp [typeALoweredVector,Module.End.mul_apply]

@[simp] theorem loweringWordWeight_nil (n : ℕ) (lam : Fin n → ℤ) (i : Fin n) : loweringWordWeight n lam [] i=lam i := by simp [loweringWordWeight]

theorem loweringWordWeight_cons (n : ℕ) (lam : Fin n → ℤ) (j : Fin n) (w : List (Fin n)) (i : Fin n) :
    loweringWordWeight n lam (j::w) i=loweringWordWeight n lam w i-typeACartan n i j := by
  simp only [loweringWordWeight,List.map_cons,List.sum_cons]
  ring

/-- Actual Cartan spectra of every lowering word, proved for every full
algebra representation and every independently specified highest weight. -/
theorem typeALoweredVector_K (q : K) (hq : q≠0) (n : ℕ) (ρ : UqTypeA q n →ₐ[K] Module.End K V)
    (v : V) (lam : Fin n → ℤ) (hv : ∀ i,ρ (typeAAlgebraGenerator q n i 2) v=q^(lam i) • v)
    (w : List (Fin n)) (i : Fin n) :
    ρ (typeAAlgebraGenerator q n i 2) (typeALoweredVector q n ρ v w)=
      q^(loweringWordWeight n lam w i) • typeALoweredVector q n ρ v w := by
  induction w with
  | nil => simpa only [typeALoweredVector_nil,loweringWordWeight_nil] using hv i
  | cons j w ih =>
    rw [typeALoweredVector_cons,← Module.End.mul_apply,← map_mul,uqA_weightF,map_smul,map_mul,
      LinearMap.smul_apply,Module.End.mul_apply,ih,map_smul,smul_smul,← zpow_add₀ hq,loweringWordWeight_cons]
    congr 1
    ring

end AMSPhysical
#print axioms AMSPhysical.typeALoweredVector_K
