import QuantumMixedFiniteCreation

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem occupationPrefix_zero (n : ℕ) (x : Fin (n+1) → ℤ) : occupationPrefix n 0 x=x 0 := by
  unfold occupationPrefix latticePairing
  rw [Finset.sum_eq_single (0:Fin (n+1))]
  · simp
  · intro k hk hk0
    have hv : ¬ k.val≤(0:Fin (n+1)).val := by
      intro h
      apply hk0
      apply Fin.ext
      simp only [Fin.val_zero] at h ⊢
      omega
    simp only [if_neg hv,zero_mul]
  · simp

theorem pairLatticeCreation_first_boundary (q : ℝ) (n l : ℕ)
    (f : OccupationPairLattice n →₀ ℝ)
    (hSupport : ∀ x y,f (x,y)≠0 → ∀ k : Fin (n+1),0≤x k)
    (y : Fin (n+1) → ℤ) :
    pairLatticeCreation q n f (Pi.single 0 ((l:ℤ)+1),y+Pi.single 0 1)=
      q^(-(l:ℤ)-y 0)*f (Pi.single 0 (l:ℤ),y) := by
  classical
  simp only [pairLatticeCreation,LinearMap.sum_apply,Finsupp.finset_sum_apply,weightedTranslation_apply]
  rw [Finset.sum_eq_single (0:Fin (n+1))]
  · have he : (Pi.single 0 ((l:ℤ)+1),y+Pi.single 0 1)-mixedCreationShift n 0=
        (Pi.single 0 (l:ℤ),y) := by
      ext k <;> simp [mixedCreationShift,Pi.single_apply] <;> split_ifs <;> omega
    rw [he]
    simp only [mixedCreationCoefficient,Fin.val_zero,pow_zero,one_mul,Nat.cast_zero,neg_zero,
      occupationPrefix_zero,Pi.single_eq_same,zero_sub]
    ring
  · intro k hk hk0
    have he : ((Pi.single 0 ((l:ℤ)+1),y+Pi.single 0 1)-mixedCreationShift n k).1 k = -1 := by
      simp [mixedCreationShift,Pi.single_apply,hk0,Ne.symm hk0]
    have hz : f ((Pi.single 0 ((l:ℤ)+1),y+Pi.single 0 1)-mixedCreationShift n k)=0 := by
      by_contra h
      have hn := hSupport _ _ h k
      change 0≤((Pi.single 0 ((l:ℤ)+1),y+Pi.single 0 1)-mixedCreationShift n k).1 k at hn
      rw [he] at hn
      omega
    rw [hz,zero_mul]
  · simp

theorem occupationTensorCoefficients_creation_boundary (q : ℝ) (n l m : ℕ)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
    (y : Fin (n+1) → ℤ) :
    occupationTensorCoefficients n (l+1) (m+1) (mixedFiniteCreation q n l m v)
        ((highestOccupation n (l+1)).val,y+Pi.single 0 1)=
      q^(-(l:ℤ)-y 0)*occupationTensorCoefficients n l m v ((highestOccupation n l).val,y) := by
  rw [occupationTensorCoefficients_creation]
  change pairLatticeCreation q n (occupationTensorCoefficients n l m v)
      (Pi.single 0 ((l+1:ℕ):ℤ),y+Pi.single 0 1)=_
  rw [Nat.cast_add,Nat.cast_one]
  apply pairLatticeCreation_first_boundary
  intro x y h k
  exact (occupationTensorCoefficients_support n l m v x y h).1.1 k

end AMSPhysical
