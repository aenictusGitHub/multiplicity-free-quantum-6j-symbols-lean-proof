import QuantumIrrepCasimir
import QuantumIntertwiner

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
noncomputable section
namespace AMSPhysical
open Module
variable {W : Type*} [AddCommGroup W] [Module ℝ W]

theorem quantumIntertwiner_Casimir (q : ℝ) (hq : 0<q) (hq1 : q≠1) (L : ℕ)
    (ρ : UqSL2 q →ₐ[ℝ] Module.End ℝ W) (T : finiteWeightSpace (K:=ℝ) L →ₗ[ℝ] W)
    (hT : IsQuantumIntertwiner (V:=finiteWeightSpace (K:=ℝ) L) (W:=W) q
      (finiteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) L) ρ T)
    (v : finiteWeightSpace (K:=ℝ) L) :
    ρ (uqCasimir q) (T v)=quantumCasimirEigen q L • T v := by
  rw [hT (uqCasimir q) v,finiteQuantumCasimir_scalar q hq hq1 L v,map_smul]

theorem quantumIntertwiner_K_basis (q : ℝ) (hq : 0<q) (hq1 : q≠1) (L : ℕ)
    (ρ : UqSL2 q →ₐ[ℝ] Module.End ℝ W) (T : finiteWeightSpace (K:=ℝ) L →ₗ[ℝ] W)
    (hT : IsQuantumIntertwiner (V:=finiteWeightSpace (K:=ℝ) L) (W:=W) q
      (finiteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) L) ρ T)
    (k : Fin (L+1)) :
    ρ (uqGenerator q 2) (T (standardWeightBasis L k))=
      q^((L:ℤ)-2*(k.val:ℤ)) • T (standardWeightBasis L k) := by
  have hg : finiteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) L (uqGenerator q 2)=
      finiteQuantumK q L := finiteQuantumRepresentation_generator q (ne_of_gt hq)
        (qInteger_denominator_ne_zero q hq hq1) L 2
  rw [hT (uqGenerator q 2) _,hg,standardWeightBasis_K,map_smul]

theorem quantumIntertwiner_highest_E (q : ℝ) (hq : 0<q) (hq1 : q≠1) (L : ℕ)
    (ρ : UqSL2 q →ₐ[ℝ] Module.End ℝ W) (T : finiteWeightSpace (K:=ℝ) L →ₗ[ℝ] W)
    (hT : IsQuantumIntertwiner (V:=finiteWeightSpace (K:=ℝ) L) (W:=W) q
      (finiteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) L) ρ T) :
    ρ (uqGenerator q 0) (T (standardWeightBasis L 0))=0 := by
  have hg : finiteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) L (uqGenerator q 0)=
      finiteQuantumE q L := finiteQuantumRepresentation_generator q (ne_of_gt hq)
        (qInteger_denominator_ne_zero q hq hq1) L 0
  rw [hT (uqGenerator q 0) _,hg,standardWeightBasis_E_zero,T.map_zero]

end AMSPhysical

#print axioms AMSPhysical.quantumIntertwiner_Casimir
