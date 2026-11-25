import QuantumTripleFirstSupport

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical

def tripleCupBase (n : ℕ) (l h c : ℤ) : OccupationTripleLattice n →₀ ℝ :=
  Finsupp.single (Pi.single 0 l,Pi.single (Fin.last n) h,Pi.single 0 c) 1

theorem tripleCupBase_first_support (n : ℕ) (l h c : ℤ) :
    CoefficientSupported (fun p : OccupationTripleLattice n =>p.1=Pi.single 0 l) (tripleCupBase n l h c) :=
  coefficientSupported_single _ _ _ rfl

theorem tripleCupBase_firstContraction_zero (q : ℝ) (n : ℕ) (hn : 0<n) (l h c : ℤ) :
    tripleFirstContraction q n (tripleCupBase n l h c)=0 := by
  have hn0 : (Fin.last n : Fin (n+1))≠0 := by intro he;have hh:=congrArg Fin.val he;simp only [Fin.val_last,Fin.val_zero] at hh;omega
  simp only [tripleFirstContraction,tripleCupBase,weightedTranslation_single,one_mul,
    tripleFirstContractionCoefficient,Pi.single_apply,if_pos rfl,ite_true,if_neg hn0,if_neg (Ne.symm hn0),qInteger_zero,mul_zero,Finsupp.single_zero]

theorem tripleCupBase_transfer (q : ℝ) (n : ℕ) (hn : 0<n) (l h c : ℤ) :
    tripleTransfer q n (tripleCupBase n l h c)=
      ((-1:ℝ)^n*q^(-(n:ℤ)-h-c)*qInteger q l) • tripleCupBase n (l-1) h (c+1) := by
  have hn0 : (Fin.last n : Fin (n+1))≠0 := by intro he;have hh:=congrArg Fin.val he;simp only [Fin.val_last,Fin.val_zero] at hh;omega
  simp only [tripleTransfer,tripleCupBase,weightedTranslation_single,one_mul,Finsupp.smul_single,smul_eq_mul,mul_one]
  have hs : (Pi.single 0 l,Pi.single (Fin.last n) h,Pi.single 0 c)+tripleTransferShift n=
      (Pi.single 0 (l-1),Pi.single (Fin.last n) h,Pi.single 0 (c+1)) := by
    ext i <;> simp [tripleTransferShift,Pi.single_apply] <;> split_ifs <;> ring
  rw [hs]
  congr 1
  simp only [tripleTransferCoefficient,Pi.single_apply,if_pos rfl,ite_true,if_neg hn0,if_neg (Ne.symm hn0),
    Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,ite_true,sub_zero]
  ring

end AMSPhysical
