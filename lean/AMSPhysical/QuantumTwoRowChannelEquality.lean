import QuantumTwoRowNormalized
import QuantumSymmetricFusionEquiv
import CyclicSpanScale

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem normalizedTwoRowChannel_eq_actual (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m : ℕ) (r : TwoRowFusionIndex l m) :
    normalizedTwoRowChannel q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      n hn l m r.val (by have h:=r.isLt;omega) (by have h:=r.isLt;omega)=
    symmetricFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m r := by
  let V:=quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m
  letI : AddCommGroup V:=inferInstance
  letI : Module ℝ V:=inferInstance
  apply algebraCyclicSpan_smul (V:=V)
  exact inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (couplingNormClosed_pos q hq (l-r.val) (m-r.val) r.val)))

theorem normalizedTwoRowChannels_orthogonal (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m : ℕ) (r s : TwoRowFusionIndex l m) (hrs : r≠s)
    (x : quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
    (hx : x∈normalizedTwoRowChannel q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      n hn l m r.val (by have h:=r.isLt;omega) (by have h:=r.isLt;omega))
    (y : quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m)
    (hy : y∈normalizedTwoRowChannel q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      n hn l m s.val (by have h:=s.isLt;omega) (by have h:=s.isLt;omega)) :
    symmetricTensorBilin q n l m x y=0 := by
  rw [normalizedTwoRowChannel_eq_actual q hq hq1] at hx hy
  exact symmetricFusionChannels_orthogonal q hq hq1 n hn l m r s hrs hy x hx

end AMSPhysical
#print axioms AMSPhysical.normalizedTwoRowChannels_orthogonal
