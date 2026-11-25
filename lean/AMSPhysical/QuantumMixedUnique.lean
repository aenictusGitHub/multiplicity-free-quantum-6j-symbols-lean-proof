import QuantumMixedRaisingCoordinate
import QuantumMixedCancellation
import QuantumOccupationScalarUnique

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3000000
noncomputable section
namespace AMSPhysical

theorem mixedTensorSum_highest_coefficients (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n r a b : ℕ)
    (f : occupationWeights (Fin (n+1)) r → ℝ)
    (hE : ∀ i : Fin n,typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      n (r+a) (r+b) (typeAAlgebraGenerator q n i 0) (mixedTensorSum n r a b f)=0) :
    ∀ t,f t=(f (highestOccupation n r)/mixedHighestCoefficient q n r b (highestOccupation n r))*
      mixedHighestCoefficient q n r b t := by
  apply occupation_scalar_unique n r f (mixedHighestCoefficient q n r b)
    (mixedHighestCoefficient_ne_zero q hq n r b)
  intro t i hi
  have hz := congrArg (fun v =>
    ((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) (r+a)).tensorProduct
      (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) (r+b))).repr v
      (shiftedOccupation n r a 0 (raisedOccupation n r t i hi),shiftedOccupation n r b (Fin.last n) t)) (hE i)
  dsimp only at hz
  rw [mixedTensorSum_E_coordinate q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n r a b i f t hi,
    map_zero,Finsupp.zero_apply] at hz
  have hc := mixedHighestCoefficient_cancellation q hq hq1 n r b t i hi
  have hcross :
      (f (raisedOccupation n r t i hi)*mixedHighestCoefficient q n r b t-
        f t*mixedHighestCoefficient q n r b (raisedOccupation n r t i hi))*qInteger q (t.val i.castSucc+1)=0 := by
    linear_combination (mixedHighestCoefficient q n r b t)*hz-f t*hc
  have hpos : 0<t.val i.castSucc+1 := by have hn := t.property.1 i.castSucc;omega
  exact sub_eq_zero.mp ((mul_eq_zero.mp hcross).resolve_right
    (ne_of_gt (qInteger_pos_real q hq hq1 _ hpos)))

/-- Uniqueness of the actual mixed highest vector in the explicitly
constructed contracted weight space, up to its single initial scalar. -/
theorem mixedTensorSum_highest_unique (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n r a b : ℕ)
    (f : occupationWeights (Fin (n+1)) r → ℝ)
    (hE : ∀ i : Fin n,typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      n (r+a) (r+b) (typeAAlgebraGenerator q n i 0) (mixedTensorSum n r a b f)=0) :
    mixedTensorSum n r a b f=
      (f (highestOccupation n r)/mixedHighestCoefficient q n r b (highestOccupation n r)) •
        mixedHighestVector q n r a b := by
  have hf := mixedTensorSum_highest_coefficients q hq hq1 n r a b f hE
  unfold mixedTensorSum mixedHighestVector
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [hf t,smul_smul]

end AMSPhysical
#print axioms AMSPhysical.mixedTensorSum_highest_unique
