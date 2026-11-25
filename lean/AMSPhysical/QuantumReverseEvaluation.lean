import QuantumReverseDualInvariant
import QuantumReverseMixedTensor
import CompactFunctionalAdjoint
import DiagonalCoevaluation

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def symmetricReverseEvaluation (q : ℝ) (n L : ℕ) :
    (quantumOccupationSpace ℝ (Fin (n+1)) L ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) L) →ₗ[ℝ] ℝ :=
  TensorProduct.lift (occupationReverseDualBilin q n L)

def symmetricReverseCoevaluation (q : ℝ) (n L : ℕ) :
    quantumOccupationSpace ℝ (Fin (n+1)) L ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) L :=
  diagonalCoevaluation (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) L)
    (fun x =>occupationDualSign n L x/occupationOppositeWeight q n L x)

theorem symmetricReverseEvaluation_generator_tmul (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n L : ℕ)
    (i : Fin n) (t : Fin 4) (v w : quantumOccupationSpace ℝ (Fin (n+1)) L) :
    symmetricReverseEvaluation q n L
      (typeAReverseMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L L
        (typeAAlgebraGenerator q n i t) (v ⊗ₜ[ℝ] w))=
      typeAQuantumCounit q n (typeAAlgebraGenerator q n i t)*symmetricReverseEvaluation q n L (v ⊗ₜ[ℝ] w) := by
  fin_cases t
  · simpa [symmetricReverseEvaluation,typeAReverseMixedTensor,typeATensorRepresentation,typeAQuantumCoproduct_generator,typeACoproductE,typeACoproductF,typeACoproductK,typeACoproductKi,typeAQuantumCounit_generator,typeAOpposite_generator,Module.endTensorEndAlgHom_apply,TensorProduct.AlgebraTensorModule.map_tmul,typeAFiniteGenerator] using typeAReverseDual_E_invariant q hq hq1 n L i v w
  · simpa [symmetricReverseEvaluation,typeAReverseMixedTensor,typeATensorRepresentation,typeAQuantumCoproduct_generator,typeACoproductE,typeACoproductF,typeACoproductK,typeACoproductKi,typeAQuantumCounit_generator,typeAOpposite_generator,Module.endTensorEndAlgHom_apply,TensorProduct.AlgebraTensorModule.map_tmul,typeAFiniteGenerator] using typeAReverseDual_F_invariant q hq hq1 n L i v w
  · simpa [symmetricReverseEvaluation,typeAReverseMixedTensor,typeATensorRepresentation,typeAQuantumCoproduct_generator,typeACoproductE,typeACoproductF,typeACoproductK,typeACoproductKi,typeAQuantumCounit_generator,typeAOpposite_generator,Module.endTensorEndAlgHom_apply,TensorProduct.AlgebraTensorModule.map_tmul,typeAFiniteGenerator] using typeAReverseDual_K_invariant q hq hq1 n L i v w
  · simpa [symmetricReverseEvaluation,typeAReverseMixedTensor,typeATensorRepresentation,typeAQuantumCoproduct_generator,typeACoproductE,typeACoproductF,typeACoproductK,typeACoproductKi,typeAQuantumCounit_generator,typeAOpposite_generator,Module.endTensorEndAlgHom_apply,TensorProduct.AlgebraTensorModule.map_tmul,typeAFiniteGenerator] using typeAReverseDual_Ki_invariant q hq hq1 n L i v w

theorem symmetricReverseEvaluation_invariant (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n L : ℕ)
    (z : UqTypeA q n)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) L ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) L) :
    symmetricReverseEvaluation q n L
      (typeAReverseMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L L z v)=
      typeAQuantumCounit q n z*symmetricReverseEvaluation q n L v := by
  apply typeA_invariantFunctional_of_generators q n _ _ _ z v
  intro i t x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v w => exact symmetricReverseEvaluation_generator_tmul q hq hq1 n L i t v w
  | add x y hx hy => simp only [map_add,LinearMap.add_apply,hx,hy,mul_add]

theorem symmetricReverseCoevaluation_adjoint (q : ℝ) (hq : 0<q) (n L : ℕ)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) L ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) L) :
    reverseMixedTensorBilin q n L L (symmetricReverseCoevaluation q n L) v=symmetricReverseEvaluation q n L v := by
  apply diagonalCoevaluation_adjoint
  intro x
  rw [div_mul_cancel₀ _ (ne_of_gt (occupationOppositeWeight_pos q hq n L x))]
  rfl

theorem symmetricReverseCoevaluation_invariant (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n L : ℕ)
    (z : UqTypeA q n) :
    typeAReverseMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L L z
      (symmetricReverseCoevaluation q n L)=typeAQuantumCounit q n z • symmetricReverseCoevaluation q n L := by
  let V := quantumOccupationSpace ℝ (Fin (n+1)) L ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) L
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  exact compact_invariantFunctional_adjoint_vector (V:=V) q n
    (typeAReverseMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n L L)
    (reverseMixedTensorBilin q n L L) (typeAReverseMixedTensor_compact q hq hq1 n L L)
    (reverseMixedTensorBilin_definite q hq n L L) (symmetricReverseEvaluation q n L)
    (symmetricReverseCoevaluation q n L) (symmetricReverseCoevaluation_adjoint q hq n L)
    (symmetricReverseEvaluation_invariant q hq hq1 n L) z

end AMSPhysical
#print axioms AMSPhysical.symmetricReverseCoevaluation_invariant
