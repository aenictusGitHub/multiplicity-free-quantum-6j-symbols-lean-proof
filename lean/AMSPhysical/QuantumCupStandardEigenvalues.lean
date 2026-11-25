import QuantumCupDiagonalDistinct

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace AMSPhysical

theorem quantumCupLeftEigenvalue_middle_add (q : ℝ) (n l m h t : ℕ) :
    quantumCupLeftEigenvalue q n l m h t=quantumCupLeftEigenvalue q n l (m+h) 0 t := by
  unfold quantumCupLeftEigenvalue
  simp only [Nat.cast_add,Nat.cast_zero]
  congr 2 <;> ring

theorem quantumCupLeftEigenvalue_swap (q : ℝ) (n l m t : ℕ) :
    quantumCupLeftEigenvalue q n l m 0 t=quantumCupLeftEigenvalue q n m l 0 t := by
  unfold quantumCupLeftEigenvalue
  congr 2 <;> ring

theorem quantumCupLeftEigenvalue_standard_shift (q : ℝ) (n : ℕ) (hn : 0<n) (l m h t : ℕ) :
    quantumCupLeftEigenvalue q n l m h t=quantumCupLeftEigenvalue q 1 l (m+(h+n-1)) 0 t := by
  unfold quantumCupLeftEigenvalue
  have hb : ((h+n-1:ℕ):ℤ)=(h:ℤ)+(n:ℤ)-1 := by omega
  simp only [Nat.cast_add,Nat.cast_zero,Nat.cast_one]
  rw [hb]
  congr 2 <;> ring

end AMSPhysical
#print axioms AMSPhysical.quantumCupLeftEigenvalue_standard_shift
