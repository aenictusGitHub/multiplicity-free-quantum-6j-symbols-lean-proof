import QuantumTypeACounit

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct
variable {K : Type*} [Field K]

theorem typeAQuantumCoproduct_left_counit (q : K) (hq : q≠0) (n : ℕ) :
    (Algebra.TensorProduct.lid K (UqTypeA q n)).toAlgHom.comp
      ((Algebra.TensorProduct.map (typeAQuantumCounit q n) (AlgHom.id K (UqTypeA q n))).comp
        (typeAQuantumCoproduct q hq n))=AlgHom.id K (UqTypeA q n) := by
  apply RingQuot.ringQuot_ext'
  apply FreeAlgebra.hom_ext
  funext it
  obtain ⟨i,t⟩ := it
  change (Algebra.TensorProduct.lid K (UqTypeA q n))
    (Algebra.TensorProduct.map (typeAQuantumCounit q n) (AlgHom.id K (UqTypeA q n))
      (typeAQuantumCoproduct q hq n (typeAAlgebraGenerator q n i t)))=typeAAlgebraGenerator q n i t
  fin_cases t <;> simp [typeAQuantumCoproduct_generator,typeAQuantumCounit_generator,
    typeACoproductE,typeACoproductF,typeACoproductK,typeACoproductKi]

theorem typeAQuantumCoproduct_right_counit (q : K) (hq : q≠0) (n : ℕ) :
    (Algebra.TensorProduct.rid K K (UqTypeA q n)).toAlgHom.comp
      ((Algebra.TensorProduct.map (AlgHom.id K (UqTypeA q n)) (typeAQuantumCounit q n)).comp
        (typeAQuantumCoproduct q hq n))=AlgHom.id K (UqTypeA q n) := by
  apply RingQuot.ringQuot_ext'
  apply FreeAlgebra.hom_ext
  funext it
  obtain ⟨i,t⟩ := it
  change (Algebra.TensorProduct.rid K K (UqTypeA q n))
    (Algebra.TensorProduct.map (AlgHom.id K (UqTypeA q n)) (typeAQuantumCounit q n)
      (typeAQuantumCoproduct q hq n (typeAAlgebraGenerator q n i t)))=typeAAlgebraGenerator q n i t
  fin_cases t <;> simp [typeAQuantumCoproduct_generator,typeAQuantumCounit_generator,
    typeACoproductE,typeACoproductF,typeACoproductK,typeACoproductKi]

end AMSPhysical
#print axioms AMSPhysical.typeAQuantumCoproduct_right_counit
