import QuantumTypeADualInvariant
import QuantumTypeADualSymmetric
import QuantumTypeATensorRepresentation
import QuantumTypeAFunctional
import FiniteWeightedDuality

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3000000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

/-- The independently constructed, nondegenerate evaluation pairing. -/
def typeADualEvaluation (q : ℝ) (n L : ℕ) :
    (quantumOccupationSpace ℝ (Fin (n+1)) L ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) L) →ₗ[ℝ] ℝ :=
  TensorProduct.lift (occupationDualBilin q n L)

def typeADualPerfectPairing (q : ℝ) (hq : 0<q) (n L : ℕ) :
    quantumOccupationSpace ℝ (Fin (n+1)) L ≃ₗ[ℝ]
      Module.Dual ℝ (quantumOccupationSpace ℝ (Fin (n+1)) L) :=
  finiteWeightedDuality (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) L)
    (occupationDualWeight q n L) (occupationDualWeight_ne_zero q hq n L)

def typeASymmetricDualTensor (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n L : ℕ) :
    UqTypeA q n →ₐ[ℝ] Module.End ℝ
      (quantumOccupationSpace ℝ (Fin (n+1)) L ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) L) :=
  typeATensorRepresentation q hq n (typeAFiniteQuantumRepresentation q hq hD n L)
    (typeAOppositeSymmetricRepresentation q hq hD n L)

theorem typeADualEvaluation_generator_tmul (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n L : ℕ)
    (i : Fin n) (t : Fin 4) (v w : quantumOccupationSpace ℝ (Fin (n+1)) L) :
    typeADualEvaluation q n L
      (typeASymmetricDualTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L
        (typeAAlgebraGenerator q n i t) (v ⊗ₜ[ℝ] w))=
      typeAQuantumCounit q n (typeAAlgebraGenerator q n i t)*typeADualEvaluation q n L (v ⊗ₜ[ℝ] w) := by
  fin_cases t
  · simpa [typeADualEvaluation,typeASymmetricDualTensor,typeATensorRepresentation,typeAQuantumCoproduct_generator,typeACoproductE,typeACoproductF,typeACoproductK,typeACoproductKi,typeAQuantumCounit_generator,typeAOpposite_generator,Module.endTensorEndAlgHom_apply,TensorProduct.AlgebraTensorModule.map_tmul,typeAFiniteGenerator] using typeADual_E_invariant q hq hq1 n L i v w
  · simpa [typeADualEvaluation,typeASymmetricDualTensor,typeATensorRepresentation,typeAQuantumCoproduct_generator,typeACoproductE,typeACoproductF,typeACoproductK,typeACoproductKi,typeAQuantumCounit_generator,typeAOpposite_generator,Module.endTensorEndAlgHom_apply,TensorProduct.AlgebraTensorModule.map_tmul,typeAFiniteGenerator] using typeADual_F_invariant q hq hq1 n L i v w
  · simpa [typeADualEvaluation,typeASymmetricDualTensor,typeATensorRepresentation,typeAQuantumCoproduct_generator,typeACoproductE,typeACoproductF,typeACoproductK,typeACoproductKi,typeAQuantumCounit_generator,typeAOpposite_generator,Module.endTensorEndAlgHom_apply,TensorProduct.AlgebraTensorModule.map_tmul,typeAFiniteGenerator] using typeADual_K_invariant q hq hq1 n L i v w
  · simpa [typeADualEvaluation,typeASymmetricDualTensor,typeATensorRepresentation,typeAQuantumCoproduct_generator,typeACoproductE,typeACoproductF,typeACoproductK,typeACoproductKi,typeAQuantumCounit_generator,typeAOpposite_generator,Module.endTensorEndAlgHom_apply,TensorProduct.AlgebraTensorModule.map_tmul,typeAFiniteGenerator] using typeADual_Ki_invariant q hq hq1 n L i v w

/-- The perfect evaluation pairing intertwines the ENTIRE actual quantum
algebra action with its counit, for every rank and symmetric degree. -/
theorem typeADualEvaluation_invariant (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n L : ℕ)
    (z : UqTypeA q n)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) L ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) L) :
    typeADualEvaluation q n L
      (typeASymmetricDualTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L z v)=
      typeAQuantumCounit q n z*typeADualEvaluation q n L v := by
  apply typeA_invariantFunctional_of_generators q n _ _ _ z v
  intro i t x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v w => exact typeADualEvaluation_generator_tmul q hq hq1 n L i t v w
  | add x y hx hy =>
    simp only [map_add,LinearMap.add_apply]
    rw [hx,hy,mul_add]

end AMSPhysical
#print axioms AMSPhysical.typeADualEvaluation_invariant
