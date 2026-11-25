import QuantumTypeALoweringWords

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3000000
noncomputable section
namespace AMSPhysical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem typeA_Ki_eigen_of_K (q : K) (hq : q≠0) (n : ℕ) (ρ : UqTypeA q n →ₐ[K] Module.End K V)
    (v : V) (i : Fin n) (a : ℤ) (hv : ρ (typeAAlgebraGenerator q n i 2) v=q^a • v) :
    ρ (typeAAlgebraGenerator q n i 3) v=q^(-a) • v := by
  have hinv : ρ (typeAAlgebraGenerator q n i 3)*ρ (typeAAlgebraGenerator q n i 2)=1 := by
    rw [← map_mul,uqA_inverse',map_one]
  have he := congrArg (fun w => ρ (typeAAlgebraGenerator q n i 3) w) hv
  dsimp only at he
  rw [← Module.End.mul_apply,hinv,Module.End.one_apply,map_smul] at he
  have hh := congrArg (fun w => q^(-a) • w) he
  dsimp only at hh
  rw [smul_smul,← zpow_add₀ hq,neg_add_cancel,zpow_zero,one_smul] at hh
  exact hh.symm

theorem typeALoweredVector_Ki (q : K) (hq : q≠0) (n : ℕ) (ρ : UqTypeA q n →ₐ[K] Module.End K V)
    (v : V) (lam : Fin n → ℤ) (hv : ∀ i,ρ (typeAAlgebraGenerator q n i 2) v=q^(lam i) • v)
    (w : List (Fin n)) (i : Fin n) :
    ρ (typeAAlgebraGenerator q n i 3) (typeALoweredVector q n ρ v w)=
      q^(-loweringWordWeight n lam w i) • typeALoweredVector q n ρ v w :=
  typeA_Ki_eigen_of_K q hq n ρ _ i _ (typeALoweredVector_K q hq n ρ v lam hv w i)

/-- Universal raising recursion on every actual lowering word. -/
theorem typeALoweredVector_E_cons (q : K) (hq : q≠0) (n : ℕ)
    (ρ : UqTypeA q n →ₐ[K] Module.End K V) (v : V) (lam : Fin n → ℤ)
    (hvK : ∀ i,ρ (typeAAlgebraGenerator q n i 2) v=q^(lam i) • v)
    (i j : Fin n) (w : List (Fin n)) :
    ρ (typeAAlgebraGenerator q n i 0) (typeALoweredVector q n ρ v (j::w))=
      ρ (typeAAlgebraGenerator q n j 1)
        (ρ (typeAAlgebraGenerator q n i 0) (typeALoweredVector q n ρ v w))+
      (if i=j then qInteger q (loweringWordWeight n lam w i) else 0) • typeALoweredVector q n ρ v w := by
  rw [typeALoweredVector_cons]
  by_cases hij : i=j
  · subst j
    rw [if_pos rfl]
    have hc : ρ (typeAAlgebraGenerator q n i 0)*ρ (typeAAlgebraGenerator q n i 1)-
        ρ (typeAAlgebraGenerator q n i 1)*ρ (typeAAlgebraGenerator q n i 0)=
        (q-q⁻¹)⁻¹ • (ρ (typeAAlgebraGenerator q n i 2)-ρ (typeAAlgebraGenerator q n i 3)) := by
      rw [← map_mul,← map_mul,← map_sub,uqA_commutator,map_smul,map_sub]
    have he := DFunLike.congr_fun hc (typeALoweredVector q n ρ v w)
    simp only [LinearMap.sub_apply,LinearMap.smul_apply,Module.End.mul_apply,
      typeALoweredVector_K q hq n ρ v lam hvK,typeALoweredVector_Ki q hq n ρ v lam hvK] at he
    rw [← sub_smul,smul_smul] at he
    have hqi : (q-q⁻¹)⁻¹*(q^(loweringWordWeight n lam w i)-q^(-loweringWordWeight n lam w i))=
        qInteger q (loweringWordWeight n lam w i) := by unfold qInteger;ring
    rw [hqi] at he
    exact (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)
  · rw [if_neg hij,zero_smul,add_zero,← Module.End.mul_apply,← map_mul,uqA_differentEF q n i j hij,
      map_mul,Module.End.mul_apply]

end AMSPhysical
#print axioms AMSPhysical.typeALoweredVector_E_cons
