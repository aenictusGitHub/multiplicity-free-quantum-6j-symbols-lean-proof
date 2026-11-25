import QuantumMixedHeight

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical

def symmetricPairGrade (n : ℕ) (p : OccupationPairLattice n) : ℤ :=
  integerOccupationHeight n p.1+integerOccupationHeight n p.2

theorem symmetricPairGrade_first_preimage (n : ℕ) (i : Fin n) (x y : Fin (n+1) → ℤ) :
    symmetricPairGrade n (x-latticeRoot i.castSucc i.succ,y)=symmetricPairGrade n (x,y)+1 := by
  unfold symmetricPairGrade
  rw [integerOccupationHeight_sub,integerOccupationHeight_root]
  ring

theorem symmetricPairGrade_second_preimage (n : ℕ) (i : Fin n) (x y : Fin (n+1) → ℤ) :
    symmetricPairGrade n (x,y-latticeRoot i.castSucc i.succ)=symmetricPairGrade n (x,y)+1 := by
  unfold symmetricPairGrade
  rw [integerOccupationHeight_sub,integerOccupationHeight_root]
  ring

theorem symmetricPairGrade_bounds (n l m : ℕ)
    (x : occupationWeights (Fin (n+1)) l) (y : occupationWeights (Fin (n+1)) m) :
    0≤symmetricPairGrade n (x.val,y.val) ∧ symmetricPairGrade n (x.val,y.val)≤((n*(l+m):ℕ):ℤ) := by
  have hx0 : 0 ≤ integerOccupationHeight n x.val := occupationHeightZ_nonnegative n l x
  have hy0 : 0 ≤ integerOccupationHeight n y.val := occupationHeightZ_nonnegative n m y
  have hx := integerOccupationHeight_upper n l x
  have hy := integerOccupationHeight_upper n m y
  unfold symmetricPairGrade
  simp only [Nat.cast_mul,Nat.cast_add]
  constructor <;> nlinarith

end AMSPhysical
