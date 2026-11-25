import QuantumSymmetricTensor
import SymmetricHighestBoundary
import SymmetricHighestExcess

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem symmetricHighest_pairRaising_zero (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n l m : ℕ)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
    (hE : ∀ i : Fin n,typeASymmetricTensor q hq hD n l m (typeAAlgebraGenerator q n i 0) v=0) :
    ∀ i : Fin n,pairSymmetricRaising q n i (occupationTensorCoefficients n l m v)=0 := by
  intro i
  rw [← occupationTensorCoefficients_symmetric_E q hq hD n l m i v,hE,map_zero]

/-- A symmetric/symmetric highest vector is determined by its genuine first-factor
highest boundary. This proves uniqueness across ALL Cartan weights. -/
theorem symmetricHighest_zero_of_boundary (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n l m : ℕ)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
    (hE : ∀ i : Fin n,typeASymmetricTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      n l m (typeAAlgebraGenerator q n i 0) v=0)
    (hBoundary : ∀ y : occupationWeights (Fin (n+1)) m,
      occupationTensorCoefficients n l m v ((highestOccupation n l).val,y.val)=0) : v=0 := by
  apply occupationTensorCoefficients_injective n l m
  rw [map_zero]
  apply pairSymmetricHighest_zero_of_boundary q hq hq1 n l
  · intro x y h
    exact (occupationTensorCoefficients_support n l m v x y h).1
  · exact symmetricHighest_pairRaising_zero q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m v hE
  · intro y
    by_cases hy : y∈occupationWeights (Fin (n+1)) m
    · exact hBoundary ⟨y,hy⟩
    · by_contra h
      exact hy (occupationTensorCoefficients_support n l m v _ y h).2

theorem symmetricHighest_coefficient_zero_of_excess (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n l m : ℕ)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
    (hE : ∀ i : Fin n,typeASymmetricTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      n l m (typeAAlgebraGenerator q n i 0) v=0)
    (i : Fin n) (x y : Fin (n+1) → ℤ) (hExcess : x i.castSucc<y i.succ) :
    occupationTensorCoefficients n l m v (x,y)=0 := by
  apply pairSymmetricHighest_zero_of_excess q hq hq1 n i _ _
    (symmetricHighest_pairRaising_zero q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m v hE i) x y hExcess
  intro x y h
  exact (occupationTensorCoefficients_support n l m v x y h).1.1 i.castSucc


end AMSPhysical
