import QuantumTypeADynkinReflection
import QuantumTypeACoproduct

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct
variable {K : Type*} [Field K]

theorem typeADynkinReflection_coproduct (q : K) (hq : q≠0) (n : ℕ) :
    (Algebra.TensorProduct.map (typeADynkinReflection q n) (typeADynkinReflection q n)).comp
      (typeAQuantumCoproduct q hq n)=
    (typeAQuantumCoproduct q hq n).comp (typeADynkinReflection q n) := by
  apply RingQuot.ringQuot_ext'
  apply FreeAlgebra.hom_ext
  funext it
  obtain ⟨i,t⟩ := it
  change Algebra.TensorProduct.map (typeADynkinReflection q n) (typeADynkinReflection q n)
      (typeAQuantumCoproduct q hq n (typeAAlgebraGenerator q n i t))=
    typeAQuantumCoproduct q hq n (typeADynkinReflection q n (typeAAlgebraGenerator q n i t))
  fin_cases t <;>
    simp [typeADynkinReflection_generator,typeAQuantumCoproduct_generator,typeACoproductE,
      typeACoproductF,typeACoproductK,typeACoproductKi]

end AMSPhysical
