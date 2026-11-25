import QuantumMixedTensor
import QuantumMixedCancellation
import QuantumOccupationEdgeSum

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3000000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem mixedFirstRaising_zero (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n r a b : ℕ) (i : Fin n)
    (t : occupationWeights (Fin (n+1)) r) (hi : t.val i.succ=0) : mixedFirstRaising q hq hD n r a b i t=0 := by
  unfold mixedFirstRaising
  rw [shiftedOccupation_high_E_zero q hq hD n r a t i hi,TensorProduct.zero_tmul,smul_zero]

theorem mixedSecondRaising_zero (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n r a b : ℕ) (i : Fin n)
    (t : occupationWeights (Fin (n+1)) r) (hi : t.val i.castSucc=0) : mixedSecondRaising q hq hD n r a b i t=0 := by
  unfold mixedSecondRaising
  rw [shiftedOccupation_low_F_zero q hq hD n r b t i hi,TensorProduct.tmul_zero,smul_zero]

theorem mixedRaising_edge_cancellation (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n r a b : ℕ) (i : Fin n)
    (t : occupationWeights (Fin (n+1)) r) (hi : 0<t.val i.succ) :
    mixedFirstRaising q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n r a b i t+
      mixedSecondRaising q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n r a b i (raisedOccupation n r t i hi)=0 := by
  unfold mixedFirstRaising mixedSecondRaising
  rw [shiftedOccupation_high_E q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n r a t i hi,
    shiftedOccupation_low_F_raised q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n r b t i hi,
    typeAFiniteGenerator_Ki_basis,
    shiftedOccupation_low_simpleWeight]
  have hneg : -(simpleOccupationWeight n t.val i-(b:ℤ)*(if i.succ=Fin.last n then 1 else 0))=
      -simpleOccupationWeight n t.val i+(b:ℤ)*(if i.succ=Fin.last n then 1 else 0) := by ring
  rw [hneg]
  simp only [← TensorProduct.smul_tmul',TensorProduct.tmul_smul,smul_smul]
  calc
    _ = (mixedHighestCoefficient q n r b t*qInteger q (t.val i.succ)*
        q^(-simpleOccupationWeight n t.val i+(b:ℤ)*(if i.succ=Fin.last n then 1 else 0))+
      mixedHighestCoefficient q n r b (raisedOccupation n r t i hi)*qInteger q (t.val i.castSucc+1)) •
        (quantumOccupationBasis (K:=ℝ) (r+a) (shiftedOccupation n r a 0 (raisedOccupation n r t i hi)) ⊗ₜ[ℝ]
        quantumOccupationBasis (K:=ℝ) (r+b) (shiftedOccupation n r b (Fin.last n) t)) := by
      module
    _ = 0 := by rw [mixedHighestCoefficient_cancellation q hq hq1 n r b t i hi,zero_smul]

/-- A completely constructed higher-rank mixed highest-weight vector is
annihilated by EVERY simple raising generator of the actual tensor action. -/
theorem mixedHighestVector_E_zero (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n r a b : ℕ) (i : Fin n) :
    typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n (r+a) (r+b)
      (typeAAlgebraGenerator q n i 0) (mixedHighestVector q n r a b)=0 := by
  rw [mixedHighestVector_E_sum]
  exact occupation_edge_sum (A:=quantumOccupationSpace ℝ (Fin (n+1)) (r+a) ⊗[ℝ]
    quantumOccupationSpace ℝ (Fin (n+1)) (r+b)) n r i _ _
    (fun t hi => mixedFirstRaising_zero q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n r a b i t hi)
    (fun t hi => mixedSecondRaising_zero q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n r a b i t hi)
    (fun t hi => mixedRaising_edge_cancellation q hq hq1 n r a b i t hi)

end AMSPhysical
#print axioms AMSPhysical.mixedHighestVector_E_zero
