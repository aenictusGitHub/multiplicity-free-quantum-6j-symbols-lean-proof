import QuantumTypeAOppositeCompact
import QuantumTypeADualSymmetric

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

section
variable (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n L : ℕ) (i : Fin n)
local notation "S" => typeAOppositeSymmetricRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L
local notation "U" => typeAAlgebraGenerator q n i

theorem typeAOppositeModule_E_adjoint : PairAdjoint (occupationOppositeBilin q n L)
    (S (U 0)) (S (U 2)*S (U 1)) := by
  simpa only [typeAOpposite_generator,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three] using typeAOppositeForm_F_adjoint q hq hq1 n L i

theorem typeAOppositeModule_F_adjoint : PairAdjoint (occupationOppositeBilin q n L)
    (S (U 1)) (S (U 0)*S (U 3)) := by
  simpa only [typeAOpposite_generator,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three] using typeAOppositeForm_E_adjoint q hq hq1 n L i

theorem typeAOppositeModule_K_adjoint : PairAdjoint (occupationOppositeBilin q n L) (S (U 2)) (S (U 2)) := by
  simpa only [typeAOpposite_generator,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three] using typeAOppositeForm_Ki_adjoint q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i

theorem typeAOppositeModule_Ki_adjoint : PairAdjoint (occupationOppositeBilin q n L) (S (U 3)) (S (U 3)) := by
  simpa only [typeAOpposite_generator,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three] using typeAOppositeForm_K_adjoint q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L i
end
end AMSPhysical
#print axioms AMSPhysical.typeAOppositeModule_E_adjoint
