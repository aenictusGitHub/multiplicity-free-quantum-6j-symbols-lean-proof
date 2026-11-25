import QuantumTripleAnnihilation
import CoefficientSupport

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical

theorem tripleRightCreation_first_support (q : ℝ) (n : ℕ) (x : Fin (n+1) → ℤ)
    (f : OccupationTripleLattice n →₀ ℝ) (hf : CoefficientSupported (fun p =>p.1=x) f) :
    CoefficientSupported (fun p : OccupationTripleLattice n =>p.1=x) (tripleRightCreation q n f) := by
  unfold tripleRightCreation
  rw [LinearMap.sum_apply]
  apply coefficientSupported_sum
  intro j
  apply coefficientSupported_weightedTranslation _ _ _ _ f hf
  intro p hp
  simpa only [tripleRightCreationShift,Prod.fst_add,add_zero] using hp

theorem tripleRightCreation_pow_first_support (q : ℝ) (n : ℕ) (x : Fin (n+1) → ℤ)
    (f : OccupationTripleLattice n →₀ ℝ) (hf : CoefficientSupported (fun p =>p.1=x) f) (t : ℕ) :
    CoefficientSupported (fun p : OccupationTripleLattice n =>p.1=x) (((tripleRightCreation q n)^t) f) := by
  induction t with
  | zero => simpa only [pow_zero,Module.End.one_apply] using hf
  | succ t ih =>
    have hP : ((tripleRightCreation q n)^(t+1)) f=
        tripleRightCreation q n (((tripleRightCreation q n)^t) f) :=
      DFunLike.congr_fun (pow_succ' (tripleRightCreation q n) t) f
    rw [hP]
    exact tripleRightCreation_first_support q n x _ ih

theorem occupationStrictPrefix_zero (n : ℕ) (x : Fin (n+1) → ℤ) :
    occupationStrictPrefix n 0 x=0 := finiteIntegerPrefix_zero (n+1) x

/-- On a pure first symmetric factor, the full adjacent annihilation reduces
exactly to its coordinate-zero contribution; no term is dropped by assumption. -/
theorem tripleLeftAnnihilation_first_support (q : ℝ) (n : ℕ) (l : ℤ)
    (f : OccupationTripleLattice n →₀ ℝ)
    (hf : CoefficientSupported (fun p =>p.1=Pi.single 0 l) f) :
    tripleLeftAnnihilation q n f=tripleFirstContraction q n f := by
  classical
  unfold tripleLeftAnnihilation
  rw [LinearMap.sum_apply,Finset.sum_eq_single (0:Fin (n+1))]
  · have hs : -tripleLeftCreationShift n 0=tripleFirstContractionShift n := by
      ext i <;> simp [tripleLeftCreationShift,tripleFirstContractionShift,Pi.single_apply] <;> split_ifs <;> ring
    have hc : tripleLeftAnnihilationCoefficient q n 0=tripleFirstContractionCoefficient q n := by
      funext p
      simp only [tripleLeftAnnihilationCoefficient,mixedAnnihilationCoefficient,
        Fin.val_zero,pow_zero,Nat.cast_zero,neg_zero,occupationStrictPrefix_zero,sub_zero,zpow_zero,one_mul]
      rfl
    rw [hs,hc]
    rfl
  · intro i hi hi0
    apply weightedTranslation_zero_on_support
    intro p hp
    have hx : p.1 i=0 := by rw [hf p hp];simp only [Pi.single_apply,if_neg hi0]
    simp only [tripleLeftAnnihilationCoefficient,mixedAnnihilationCoefficient,hx,qInteger_zero,mul_zero,zero_mul]
  · simp

end AMSPhysical
