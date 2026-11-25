import QuantumSymmetricHighestBoundary
import QuantumSymmetricGrade
import GradedCommonHighest
import BilinearCyclic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2600000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem symmetricTensorCoefficients_grade_bounds (n l m : ℕ)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
    (p : OccupationPairLattice n) (hp : occupationTensorCoefficients n l m v p≠0) :
    0≤symmetricPairGrade n p ∧ symmetricPairGrade n p≤((n*(l+m):ℕ):ℤ) := by
  obtain ⟨hx,hy⟩ := occupationTensorCoefficients_support n l m v p.1 p.2 hp
  exact symmetricPairGrade_bounds n l m ⟨p.1,hx⟩ ⟨p.2,hy⟩

theorem symmetricTensorRaising_grade_decreases (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n l m : ℕ)
    (i : Fin n) (v : quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
    (k : ℕ) (hBound : ∀ p,occupationTensorCoefficients n l m v p≠0 → symmetricPairGrade n p≤(k:ℤ))
    (p : OccupationPairLattice n)
    (hp : occupationTensorCoefficients n l m
      (typeASymmetricTensor q hq hD n l m (typeAAlgebraGenerator q n i 0) v) p≠0) :
    symmetricPairGrade n p<(k:ℤ) := by
  rcases p with ⟨x,y⟩
  rw [occupationTensorCoefficients_symmetric_E,pairSymmetricRaising_coordinate] at hp
  by_cases hpre : occupationTensorCoefficients n l m v (x-latticeRoot i.castSucc i.succ,y)=0
  · have hpre' : occupationTensorCoefficients n l m v (x,y-latticeRoot i.castSucc i.succ)≠0 := by
      intro hz
      apply hp
      rw [hpre,hz,zero_mul,zero_mul,zero_mul,zero_add]
    have hb := hBound (x,y-latticeRoot i.castSucc i.succ) hpre'
    rw [symmetricPairGrade_second_preimage] at hb
    omega
  · have hb := hBound (x-latticeRoot i.castSucc i.succ,y) hpre
    rw [symmetricPairGrade_first_preimage] at hb
    omega

/-- Every nonzero actual invariant subspace of the symmetric tensor product
contains a nonzero common highest vector. The bounded grading and strict
raising decrease are constructed, not postulated. -/
theorem symmetricInvariant_exists_highest (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n l m : ℕ)
    (S : Submodule ℝ (quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m))
    (hS : algebraInvariant
      (V:=quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
      (typeASymmetricTensor q hq hD n l m) S) (hS0 : S≠⊥) :
    ∃ w,w∈S ∧ w≠0 ∧ ∀ i : Fin n,typeASymmetricTensor q hq hD n l m (typeAAlgebraGenerator q n i 0) w=0 := by
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS0
  apply commonHighest_of_decreasing_coefficients
    (occupationTensorCoefficients n l m) (occupationTensorCoefficients_injective n l m)
    (symmetricPairGrade n)
    (fun i : Fin n => typeASymmetricTensor q hq hD n l m (typeAAlgebraGenerator q n i 0))
    (fun v p hp => (symmetricTensorCoefficients_grade_bounds n l m v p hp).1)
    (fun i v k => symmetricTensorRaising_grade_decreases q hq hD n l m i v k)
    S (fun i v hv => hS (typeAAlgebraGenerator q n i 0) v hv) (n*(l+m)) v hv hv0
  intro p hp
  exact (symmetricTensorCoefficients_grade_bounds n l m v p hp).2

end AMSPhysical
