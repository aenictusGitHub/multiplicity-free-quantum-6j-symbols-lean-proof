import QuantumReverseDualForm

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical
section
variable (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n L : ℕ) (i : Fin n)
local notation "G" => typeAFiniteGenerator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i
local notation "B" => occupationReverseDualBilin q n L

theorem typeAReverseDual_E_invariant (v w : quantumOccupationSpace ℝ (Fin (n+1)) L) :
    B (G 1 v) (G 2 w)+B v (G 0 w)=0 := by
  have h:=typeAReverseDual_F_adjoint q hq hq1 n L i v (G 2 w)
  change B (G 1 v) (G 2 w)=B v (-(G 0 (G 3 (G 2 w)))) at h
  have hw:=DFunLike.congr_fun (typeADual_Ki_K q hq hq1 n L i) w
  change G 3 (G 2 w)=w at hw
  rw [hw,map_neg] at h
  linarith

theorem typeAReverseDual_F_invariant (v w : quantumOccupationSpace ℝ (Fin (n+1)) L) :
    B (G 0 v) w+B (G 2 v) (G 1 w)=0 := by
  have h:=typeAReverseDual_E_adjoint q hq hq1 n L i v w
  change B (G 0 v) w=B v (-(G 2 (G 1 w))) at h
  rw [map_neg] at h
  have hk:=typeAReverseDual_K_adjoint q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i v (G 1 w)
  linarith

theorem typeAReverseDual_K_invariant (v w : quantumOccupationSpace ℝ (Fin (n+1)) L) :
    B (G 3 v) (G 2 w)=B v w := by
  rw [typeAReverseDual_Ki_adjoint q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i]
  have hw:=DFunLike.congr_fun (typeADual_Ki_K q hq hq1 n L i) w
  change G 3 (G 2 w)=w at hw
  rw [hw]

theorem typeAReverseDual_Ki_invariant (v w : quantumOccupationSpace ℝ (Fin (n+1)) L) :
    B (G 2 v) (G 3 w)=B v w := by
  rw [typeAReverseDual_K_adjoint q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i]
  have hw:=DFunLike.congr_fun (typeADual_K_Ki q hq hq1 n L i) w
  change G 2 (G 3 w)=w at hw
  rw [hw]
end
end AMSPhysical
