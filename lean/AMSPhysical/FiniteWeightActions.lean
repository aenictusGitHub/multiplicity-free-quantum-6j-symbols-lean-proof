import QuantumClebschMap

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
noncomputable section
namespace AMSPhysical
open Module

variable {K : Type*} [Field K]

theorem standardWeightBasis_K (q : K) (L : ℕ) (k : Fin (L+1)) :
    finiteQuantumK q L (standardWeightBasis L k)=
      q^((L:ℤ)-2*(k.val:ℤ)) • standardWeightBasis L k := by
  rw [standardWeightBasis_apply]
  apply Subtype.ext
  change quantumK q L (Finsupp.single (k.val:ℤ) 1)=
    q^((L:ℤ)-2*(k.val:ℤ)) • Finsupp.single (k.val:ℤ) 1
  simp only [quantumK,weightShift_single,add_zero,one_mul,Finsupp.smul_single,smul_eq_mul,mul_one]

theorem standardWeightBasis_E_zero (q : K) (L : ℕ) :
    finiteQuantumE q L (standardWeightBasis L 0)=0 := by
  rw [standardWeightBasis_apply]
  apply Subtype.ext
  change quantumE q (Finsupp.single 0 1)=0
  simp only [quantumE,weightShift_single,qInteger_zero,mul_zero,Finsupp.single_zero]

theorem standardWeightBasis_E_succ (q : K) (L : ℕ) (k : Fin L) :
    finiteQuantumE q L (standardWeightBasis L k.succ)=
      qInteger q (k.val+1:ℕ) • standardWeightBasis L k.castSucc := by
  rw [standardWeightBasis_apply,standardWeightBasis_apply]
  apply Subtype.ext
  change quantumE q (Finsupp.single ((k.val+1:ℕ):ℤ) 1)=
    qInteger q (k.val+1:ℕ) • Finsupp.single (k.val:ℤ) 1
  simp only [quantumE,weightShift_single,one_mul,Nat.cast_add,Nat.cast_one,
    Finsupp.smul_single,smul_eq_mul,mul_one]
  congr 1
  omega

theorem standardWeightBasis_F_castSucc (q : K) (L : ℕ) (k : Fin L) :
    finiteQuantumF q L (standardWeightBasis L k.castSucc)=
      qInteger q ((L:ℤ)-(k.val:ℤ)) • standardWeightBasis L k.succ := by
  rw [standardWeightBasis_apply,standardWeightBasis_apply]
  apply Subtype.ext
  change quantumF q L (Finsupp.single (k.val:ℤ) 1)=
    qInteger q ((L:ℤ)-(k.val:ℤ)) • Finsupp.single ((k.val+1:ℕ):ℤ) 1
  simp only [quantumF,weightShift_single,one_mul,Nat.cast_add,Nat.cast_one,
    Finsupp.smul_single,smul_eq_mul,mul_one]

theorem standardWeightBasis_F_last (q : K) (L : ℕ) :
    finiteQuantumF q L (standardWeightBasis L (Fin.last L))=0 := by
  rw [standardWeightBasis_apply]
  apply Subtype.ext
  change quantumF q L (Finsupp.single (L:ℤ) 1)=0
  simp only [quantumF,weightShift_single,sub_self,qInteger_zero,mul_zero,Finsupp.single_zero]

end AMSPhysical

#print axioms AMSPhysical.standardWeightBasis_E_succ
