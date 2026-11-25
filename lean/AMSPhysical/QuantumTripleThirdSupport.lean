import QuantumRightTransferDefinitions
import CoefficientSupport
import QuantumTripleCupBase

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical

theorem tripleLeftCreation_third_support (q : ℝ) (n : ℕ) (z : Fin (n+1) → ℤ)
    (f : OccupationTripleLattice n →₀ ℝ) (hf : CoefficientSupported (fun p =>p.2.2=z) f) :
    CoefficientSupported (fun p : OccupationTripleLattice n =>p.2.2=z) (tripleLeftCreation q n f) := by
  unfold tripleLeftCreation
  rw [LinearMap.sum_apply]
  apply coefficientSupported_sum
  intro j
  apply coefficientSupported_weightedTranslation _ _ _ _ f hf
  intro p hp
  simpa only [tripleLeftCreationShift,Prod.snd_add,add_zero] using hp

theorem tripleLeftCreation_pow_third_support (q : ℝ) (n : ℕ) (z : Fin (n+1) → ℤ)
    (f : OccupationTripleLattice n →₀ ℝ) (hf : CoefficientSupported (fun p =>p.2.2=z) f) (t : ℕ) :
    CoefficientSupported (fun p : OccupationTripleLattice n =>p.2.2=z) (((tripleLeftCreation q n)^t) f) := by
  induction t with
  | zero => simpa only [pow_zero,Module.End.one_apply] using hf
  | succ t ih =>
    have hP : ((tripleLeftCreation q n)^(t+1)) f=
        tripleLeftCreation q n (((tripleLeftCreation q n)^t) f) :=
      DFunLike.congr_fun (pow_succ' (tripleLeftCreation q n) t) f
    rw [hP]
    exact tripleLeftCreation_third_support q n z _ ih

theorem tripleRightAnnihilation_third_support (q : ℝ) (n : ℕ) (c : ℤ)
    (f : OccupationTripleLattice n →₀ ℝ)
    (hf : CoefficientSupported (fun p =>p.2.2=Pi.single 0 c) f) :
    tripleRightAnnihilation q n f=tripleLastContraction q n f := by
  classical
  unfold tripleRightAnnihilation
  rw [LinearMap.sum_apply,Finset.sum_eq_single (0:Fin (n+1))]
  · have hs : -tripleRightCreationShift n 0=tripleLastContractionShift n := by
      ext i <;> simp [tripleRightCreationShift,tripleLastContractionShift,Pi.single_apply] <;> split_ifs <;> ring
    have hc : tripleRightAnnihilationCoefficient q n 0=tripleLastContractionCoefficient q n := by
      funext p
      exact tripleRightAnnihilationCoefficient_zero q n p
    rw [hs,hc]
    rfl
  · intro i hi hi0
    apply weightedTranslation_zero_on_support
    intro p hp
    have hz : occupationLatticeReflect n p.2.2 i.rev=0 := by
      change p.2.2 i.rev.rev=0
      rw [Fin.rev_rev,hf p hp]
      simp only [Pi.single_apply,if_neg hi0]
    simp only [tripleRightAnnihilationCoefficient,mixedAnnihilationCoefficient,hz,qInteger_zero,mul_zero]
  · simp

theorem tripleCupBase_third_support (n : ℕ) (l h c : ℤ) :
    CoefficientSupported (fun p : OccupationTripleLattice n =>p.2.2=Pi.single 0 c) (tripleCupBase n l h c) :=
  coefficientSupported_single _ _ _ rfl

theorem tripleCupBase_lastContraction_zero (q : ℝ) (n : ℕ) (hn : 0<n) (l h c : ℤ) :
    tripleLastContraction q n (tripleCupBase n l h c)=0 := by
  have hn0 : (Fin.last n : Fin (n+1))≠0 := by intro he;have hh:=congrArg Fin.val he;simp only [Fin.val_last,Fin.val_zero] at hh;omega
  simp only [tripleLastContraction,tripleCupBase,weightedTranslation_single,one_mul,
    tripleLastContractionCoefficient,Pi.single_apply,if_pos rfl,ite_true,
    if_neg hn0,if_neg (Ne.symm hn0),qInteger_zero,mul_zero,zero_mul,Finsupp.single_zero]

theorem tripleCupBase_reverseTransfer (q : ℝ) (hq : q≠0) (n : ℕ) (hn : 0<n) (l h c : ℤ) :
    tripleReverseTransfer q n (tripleCupBase n l h c)=
      ((-1:ℝ)^n*q^(-(n:ℤ)-h-l)*qInteger q c) • tripleCupBase n (l+1) h (c-1) := by
  have hn0 : (Fin.last n : Fin (n+1))≠0 := by intro he;have hh:=congrArg Fin.val he;simp only [Fin.val_last,Fin.val_zero] at hh;omega
  simp only [tripleReverseTransfer,tripleCupBase,weightedTranslation_single,one_mul,Finsupp.smul_single,smul_eq_mul,mul_one]
  have hs : (Pi.single 0 l,Pi.single (Fin.last n) h,Pi.single 0 c)+tripleReverseTransferShift n=
      (Pi.single 0 (l+1),Pi.single (Fin.last n) h,Pi.single 0 (c-1)) := by
    ext i <;> simp [tripleReverseTransferShift,Pi.single_apply] <;> split_ifs <;> ring
  rw [hs]
  congr 1
  simp only [tripleReverseTransferCoefficient,tripleLastContractionPrefactor,Pi.single_apply,
    if_pos rfl,ite_true,if_neg hn0,if_neg (Ne.symm hn0),
    Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,ite_true,add_zero]
  have hp : q^(-(n:ℤ)-h-c+c)*q^(-l)=q^(-(n:ℤ)-h-l) := by
    rw [← zpow_add₀ hq]
    congr 1
    ring
  linear_combination ((-1:ℝ)^n*qInteger q c)*hp

end AMSPhysical
