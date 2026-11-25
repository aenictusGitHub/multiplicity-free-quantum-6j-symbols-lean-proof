import QuantumTypeADualForm

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3000000
noncomputable section
namespace AMSPhysical

section
variable (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n L : ℕ) (i : Fin n)
local notation "G" => typeAFiniteGenerator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i
local notation "B" => occupationDualBilin q n L

theorem typeADual_K_Ki : G 2*G 3=1 := by
  unfold typeAFiniteGenerator
  rw [← map_mul,uqA_inverse,map_one]

theorem typeADual_Ki_K : G 3*G 2=1 := by
  unfold typeAFiniteGenerator
  rw [← map_mul,uqA_inverse',map_one]

theorem typeADual_E_invariant (v w : quantumOccupationSpace ℝ (Fin (n+1)) L) :
    B (G 0 v) (G 3 w)+B v (G 1 w)=0 := by
  have he := typeADual_E_adjoint q hq hq1 n L i v (G 3 w)
  change B (G 0 v) (G 3 w)=B v (-(G 1 (G 2 (G 3 w)))) at he
  have hw := DFunLike.congr_fun (typeADual_K_Ki q hq hq1 n L i) w
  change G 2 (G 3 w)=w at hw
  rw [hw,map_neg] at he
  linarith

theorem typeADual_F_invariant (v w : quantumOccupationSpace ℝ (Fin (n+1)) L) :
    B (G 1 v) w+B (G 3 v) (G 0 w)=0 := by
  have he := typeADual_F_adjoint q hq hq1 n L i v w
  change B (G 1 v) w=B v (-(G 3 (G 0 w))) at he
  rw [map_neg] at he
  have hk := typeADual_Ki_adjoint q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i v (G 0 w)
  linarith

theorem typeADual_K_invariant (v w : quantumOccupationSpace ℝ (Fin (n+1)) L) :
    B (G 2 v) (G 3 w)=B v w := by
  rw [typeADual_K_adjoint q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i]
  have hw := DFunLike.congr_fun (typeADual_K_Ki q hq hq1 n L i) w
  change G 2 (G 3 w)=w at hw
  rw [hw]

theorem typeADual_Ki_invariant (v w : quantumOccupationSpace ℝ (Fin (n+1)) L) :
    B (G 3 v) (G 2 w)=B v w := by
  rw [typeADual_Ki_adjoint q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i]
  have hw := DFunLike.congr_fun (typeADual_Ki_K q hq hq1 n L i) w
  change G 3 (G 2 w)=w at hw
  rw [hw]
end
end AMSPhysical
#print axioms AMSPhysical.typeADual_E_invariant
