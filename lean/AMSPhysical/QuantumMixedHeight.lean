import QuantumPairCoordinates
import QuantumOccupationGraph

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
noncomputable section
namespace AMSPhysical

def integerOccupationHeight (n : ℕ) (x : Fin (n+1) → ℤ) : ℤ :=
  latticePairing (fun k : Fin (n+1) => (k.val:ℤ)) x

theorem integerOccupationHeight_add (n : ℕ) (x y : Fin (n+1) → ℤ) :
    integerOccupationHeight n (x+y)=integerOccupationHeight n x+integerOccupationHeight n y :=
  latticePairing_add_right _ _ _

theorem integerOccupationHeight_sub (n : ℕ) (x y : Fin (n+1) → ℤ) :
    integerOccupationHeight n (x-y)=integerOccupationHeight n x-integerOccupationHeight n y := by
  simp only [integerOccupationHeight,latticePairing,Pi.sub_apply,mul_sub,Finset.sum_sub_distrib]

theorem integerOccupationHeight_root (n : ℕ) (i : Fin n) :
    integerOccupationHeight n (latticeRoot i.castSucc i.succ)= -1 := by
  unfold integerOccupationHeight
  rw [latticePairing_root_right]
  simp only [Fin.coe_castSucc,Fin.val_succ,Nat.cast_add,Nat.cast_one]
  ring

theorem integerOccupationHeight_upper (n L : ℕ) (x : occupationWeights (Fin (n+1)) L) :
    integerOccupationHeight n x.val≤(n:ℤ)*L := by
  calc
    _ = ∑ k : Fin (n+1),(k.val:ℤ)*x.val k := rfl
    _ ≤ ∑ k : Fin (n+1),(n:ℤ)*x.val k := by
      apply Finset.sum_le_sum
      intro k hk
      apply mul_le_mul_of_nonneg_right _ (x.property.1 k)
      exact_mod_cast Nat.le_of_lt_succ k.isLt
    _ = (n:ℤ)*L := by rw [← Finset.mul_sum,x.property.2]

/-- A nonnegative, bounded grading on every actual mixed tensor basis pair. -/
def mixedPairGrade (n m : ℕ) (p : OccupationPairLattice n) : ℤ :=
  integerOccupationHeight n p.1-integerOccupationHeight n p.2+((n*m:ℕ):ℤ)

theorem mixedPairGrade_first_preimage (n m : ℕ) (i : Fin n) (x y : Fin (n+1) → ℤ) :
    mixedPairGrade n m (x-latticeRoot i.castSucc i.succ,y)=mixedPairGrade n m (x,y)+1 := by
  unfold mixedPairGrade
  rw [integerOccupationHeight_sub,integerOccupationHeight_root]
  ring

theorem mixedPairGrade_second_preimage (n m : ℕ) (i : Fin n) (x y : Fin (n+1) → ℤ) :
    mixedPairGrade n m (x,y+latticeRoot i.castSucc i.succ)=mixedPairGrade n m (x,y)+1 := by
  unfold mixedPairGrade
  rw [integerOccupationHeight_add,integerOccupationHeight_root]
  ring

theorem mixedPairGrade_bounds (n l m : ℕ)
    (x : occupationWeights (Fin (n+1)) l) (y : occupationWeights (Fin (n+1)) m) :
    0≤mixedPairGrade n m (x.val,y.val) ∧ mixedPairGrade n m (x.val,y.val)≤((n*(l+m):ℕ):ℤ) := by
  have hx0 : 0 ≤ integerOccupationHeight n x.val := occupationHeightZ_nonnegative n l x
  have hy0 : 0 ≤ integerOccupationHeight n y.val := occupationHeightZ_nonnegative n m y
  have hx := integerOccupationHeight_upper n l x
  have hy := integerOccupationHeight_upper n m y
  unfold mixedPairGrade
  simp only [Nat.cast_mul,Nat.cast_add]
  constructor <;> nlinarith

end AMSPhysical
