import QuantumTypeACoproduct

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

variable {K : Type*} [Field K]

/-- Tensor products of the independently presented quantum algebra are associative. -/
theorem typeAQuantumCoproduct_coassociative (q : K) (hq : q≠0) (n : ℕ) :
    ((Algebra.TensorProduct.assoc K K (UqTypeA q n) (UqTypeA q n) (UqTypeA q n)).toAlgHom.comp
      ((Algebra.TensorProduct.map (typeAQuantumCoproduct q hq n) (AlgHom.id K (UqTypeA q n))).comp
        (typeAQuantumCoproduct q hq n)))=
    (Algebra.TensorProduct.map (AlgHom.id K (UqTypeA q n)) (typeAQuantumCoproduct q hq n)).comp
      (typeAQuantumCoproduct q hq n) := by
  apply RingQuot.ringQuot_ext'
  apply FreeAlgebra.hom_ext
  funext it
  obtain ⟨i,t⟩ := it
  change (Algebra.TensorProduct.assoc K K (UqTypeA q n) (UqTypeA q n) (UqTypeA q n))
    ((Algebra.TensorProduct.map (typeAQuantumCoproduct q hq n) (AlgHom.id K (UqTypeA q n)))
      (typeAQuantumCoproduct q hq n (typeAAlgebraGenerator q n i t)))=
    (Algebra.TensorProduct.map (AlgHom.id K (UqTypeA q n)) (typeAQuantumCoproduct q hq n))
      (typeAQuantumCoproduct q hq n (typeAAlgebraGenerator q n i t))
  fin_cases t <;> simp [typeAQuantumCoproduct_generator,typeACoproductE,typeACoproductF,typeACoproductK,
    typeACoproductKi,TensorProduct.add_tmul,TensorProduct.tmul_add,Algebra.TensorProduct.one_def,add_assoc]

end AMSPhysical

#print axioms AMSPhysical.typeAQuantumCoproduct_coassociative
