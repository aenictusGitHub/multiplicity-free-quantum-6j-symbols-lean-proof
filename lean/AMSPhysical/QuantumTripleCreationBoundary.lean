import QuantumTriplePositiveSupport
import QuantumCreationBoundary

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical

theorem tripleLeftCreation_first_boundary (q : ℝ) (n : ℕ) (l : ℤ)
    (f : OccupationTripleLattice n →₀ ℝ) (hf : CoefficientSupported (tripleOccupationNonnegative n) f)
    (y z : Fin (n+1) → ℤ) :
    tripleLeftCreation q n f (Pi.single 0 (l+1),y+Pi.single 0 1,z)=
      q^(-l-y 0)*f (Pi.single 0 l,y,z) := by
  classical
  simp only [tripleLeftCreation,LinearMap.sum_apply,Finsupp.finset_sum_apply,weightedTranslation_apply]
  rw [Finset.sum_eq_single (0:Fin (n+1))]
  · have he : (Pi.single 0 (l+1),y+Pi.single 0 1,z)-tripleLeftCreationShift n 0=(Pi.single 0 l,y,z) := by
      ext i <;> simp [tripleLeftCreationShift,Pi.single_apply] <;> split_ifs <;> ring
    rw [he]
    simp only [tripleLeftCreationCoefficient,mixedCreationCoefficient,Fin.val_zero,pow_zero,one_mul,Nat.cast_zero,neg_zero,
      occupationPrefix_zero,Pi.single_eq_same,zero_sub]
    ring
  · intro j hj hj0
    have he : ((Pi.single 0 (l+1),y+Pi.single 0 1,z)-tripleLeftCreationShift n j).1 j= -1 := by
      simp [tripleLeftCreationShift,Pi.single_apply,hj0,Ne.symm hj0]
    have hz : f ((Pi.single 0 (l+1),y+Pi.single 0 1,z)-tripleLeftCreationShift n j)=0 := by
      by_contra h
      have hn:=(hf _ h).1 j
      rw [he] at hn
      omega
    rw [hz,zero_mul]
  · simp

theorem tripleRightCreation_middle_boundary (q : ℝ) (n : ℕ) (h : ℤ)
    (f : OccupationTripleLattice n →₀ ℝ) (hf : CoefficientSupported (tripleOccupationNonnegative n) f)
    (x z : Fin (n+1) → ℤ) :
    tripleRightCreation q n f (x,Pi.single (Fin.last n) (h+1),z+Pi.single (Fin.last n) 1)=
      q^(-h-z (Fin.last n))*f (x,Pi.single (Fin.last n) h,z) := by
  classical
  simp only [tripleRightCreation,LinearMap.sum_apply,Finsupp.finset_sum_apply,weightedTranslation_apply]
  rw [Finset.sum_eq_single (Fin.last n)]
  · have he : (x,Pi.single (Fin.last n) (h+1),z+Pi.single (Fin.last n) 1)-tripleRightCreationShift n (Fin.last n)=
        (x,Pi.single (Fin.last n) h,z) := by
      ext i <;> simp [tripleRightCreationShift,Pi.single_apply] <;> split_ifs <;> ring
    rw [he]
    simp only [tripleRightCreationCoefficient,mixedCreationCoefficient,Fin.rev_last,Fin.val_zero,
      pow_zero,one_mul,Nat.cast_zero,neg_zero,occupationPrefix_zero,occupationLatticeReflect,
      Fin.rev_zero,Pi.single_eq_same,zero_sub]
    rw [Fin.rev_zero,Pi.single_eq_same]
    ring
  · intro j hj hjn
    have he : ((x,Pi.single (Fin.last n) (h+1),z+Pi.single (Fin.last n) 1)-tripleRightCreationShift n j).2.1 j= -1 := by
      simp [tripleRightCreationShift,Pi.single_apply,hjn,Ne.symm hjn]
    have hz : f ((x,Pi.single (Fin.last n) (h+1),z+Pi.single (Fin.last n) 1)-tripleRightCreationShift n j)=0 := by
      by_contra hz
      have hn:=(hf _ hz).2.1 j
      rw [he] at hn
      omega
    rw [hz,zero_mul]
  · simp

end AMSPhysical
