import OppositeLoweringCharge
import QuantumReverseMixedTensor

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def mixedFirstBoundaryFunctional (n p s : ℕ) :=
  (occupationHighestFunctional n s).comp
    (tensorFirstFunctional (W:=quantumOccupationSpace ℝ (Fin (n+1)) s) (occupationHighestFunctional n p))

def reverseMixedFirstBoundaryFunctional (n p s : ℕ) :=
  (occupationHighestFunctional n s).comp
    (tensorLastFunctional (W:=quantumOccupationSpace ℝ (Fin (n+1)) s) (occupationHighestFunctional n p))

/-- Forward and reversed mixed orientations have exactly the same boundary
phase on every lowering word. The ratio is the positive scalar q^(p*s),
even when the internal weight space has multiplicity greater than one. -/
theorem mixed_orientation_word_boundary (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (n : ℕ) (hn : 0<n) (p s : ℕ) (w : List (Fin n)) :
    reverseMixedFirstBoundaryFunctional n p s
      (typeALoweredVector q n (typeAReverseMixedTensor q hq hD n s p)
        (quantumOccupationBasis (K:=ℝ) s (lowestOccupation n s) ⊗ₜ[ℝ]
          quantumOccupationBasis (K:=ℝ) p (highestOccupation n p)) w) =
      q^((p:ℤ)*(s:ℤ))* mixedFirstBoundaryFunctional n p s
        (typeALoweredVector q n (typeAMixedTensor q hq hD n p s)
          (quantumOccupationBasis (K:=ℝ) p (highestOccupation n p) ⊗ₜ[ℝ]
            quantumOccupationBasis (K:=ℝ) s (lowestOccupation n s)) w) := by
  let ρ:=typeAFiniteQuantumRepresentation q hq hD n p
  let σ:=typeAOppositeSymmetricRepresentation q hq hD n s
  let e:=occupationHighestFunctional n p
  have hF : ∀ i x,e (ρ (typeAAlgebraGenerator q n i 1) x)=0 :=
    occupationHighestFunctional_F q hq hD n p
  have hK : ∀ i x,e (ρ (typeAAlgebraGenerator q n i 3) x)=
      q^(-(p:ℤ)*(if i.castSucc=0 then 1 else 0))*e x :=
    occupationHighestFunctional_Ki q hq hD n p
  have hL:=tensorFirstFunctional_lowering q hq n ρ σ e
    (fun i=>q^(-(p:ℤ)*(if i.castSucc=0 then 1 else 0))) hF hK
    (quantumOccupationBasis (K:=ℝ) p (highestOccupation n p))
    (occupationHighestFunctional_highest n p)
    (quantumOccupationBasis (K:=ℝ) s (lowestOccupation n s)) w
  have hR:=tensorLastFunctional_lowering q hq n ρ σ e hF
    (quantumOccupationBasis (K:=ℝ) p (highestOccupation n p))
    (occupationHighestFunctional_highest n p)
    (quantumOccupationBasis (K:=ℝ) s (lowestOccupation n s)) w
  change occupationHighestFunctional n s (tensorLastFunctional e
    (typeALoweredVector q n (typeATensorRepresentation q hq n σ ρ) _ w)) =
    q^((p:ℤ)*(s:ℤ))*occupationHighestFunctional n s (tensorFirstFunctional e
      (typeALoweredVector q n (typeATensorRepresentation q hq n ρ σ) _ w))
  rw [hR,hL,map_smul,smul_eq_mul,loweringZeroCharge_product q hq]
  let z:=occupationHighestFunctional n s (typeALoweredVector q n σ
    (quantumOccupationBasis (K:=ℝ) s (lowestOccupation n s)) w)
  by_cases hz:z=0
  · change z=_*(_*z)
    rw [hz,mul_zero,mul_zero]
  · have hc:=oppositeLowered_first_nonzero_charge q hq hD n hn s w hz
    rw [hc]
    have hp : q^((p:ℤ)*(s:ℤ))*q^(-(p:ℤ)*(s:ℤ))=1 := by
      rw [← zpow_add₀ hq]
      simp only [neg_mul,add_neg_cancel,zpow_zero]
    rw [← mul_assoc,hp,one_mul]

end AMSPhysical
#print axioms AMSPhysical.mixed_orientation_word_boundary
