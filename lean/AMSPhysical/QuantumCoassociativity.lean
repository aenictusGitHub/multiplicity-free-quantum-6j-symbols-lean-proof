import QuantumCoproduct

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

variable {K : Type*} [Field K]

/-- Tensor products of the independently presented quantum algebra are associative. -/
theorem quantumCoproduct_coassociative (q : K) (hq : q≠0) :
    ((Algebra.TensorProduct.assoc K K (UqSL2 q) (UqSL2 q) (UqSL2 q)).toAlgHom.comp
      ((Algebra.TensorProduct.map (quantumCoproduct q hq) (AlgHom.id K (UqSL2 q))).comp
        (quantumCoproduct q hq)))=
    (Algebra.TensorProduct.map (AlgHom.id K (UqSL2 q)) (quantumCoproduct q hq)).comp
      (quantumCoproduct q hq) := by
  apply RingQuot.ringQuot_ext'
  apply FreeAlgebra.hom_ext
  funext i
  change (Algebra.TensorProduct.assoc K K (UqSL2 q) (UqSL2 q) (UqSL2 q))
    ((Algebra.TensorProduct.map (quantumCoproduct q hq) (AlgHom.id K (UqSL2 q)))
      (quantumCoproduct q hq (uqGenerator q i)))=
    (Algebra.TensorProduct.map (AlgHom.id K (UqSL2 q)) (quantumCoproduct q hq))
      (quantumCoproduct q hq (uqGenerator q i))
  fin_cases i <;> simp [quantumCoproduct_generator,coproductE,coproductF,coproductK,
    coproductKinv,TensorProduct.add_tmul,TensorProduct.tmul_add,Algebra.TensorProduct.one_def,add_assoc]

end AMSPhysical

#print axioms AMSPhysical.quantumCoproduct_coassociative
