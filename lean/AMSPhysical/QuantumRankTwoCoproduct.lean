import QuantumRankTwoAlgebra
import QuantumTypeACoproduct

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
variable {K : Type*} [Field K]

/-- The presentation isomorphism also preserves the actual coproduct,
so it identifies tensor representations, not just individual modules. -/
theorem rankTwoToSL2_coproduct (q : K) (hq : q≠0) :
    (Algebra.TensorProduct.map (rankTwoToSL2 q) (rankTwoToSL2 q)).comp
        (typeAQuantumCoproduct q hq 1)=
      (quantumCoproduct q hq).comp (rankTwoToSL2 q) := by
  apply RingQuot.ringQuot_ext'
  apply FreeAlgebra.hom_ext
  funext it
  obtain ⟨i,t⟩:=it
  change Algebra.TensorProduct.map (rankTwoToSL2 q) (rankTwoToSL2 q)
    (typeAQuantumCoproduct q hq 1 (typeAAlgebraGenerator q 1 i t))=
    quantumCoproduct q hq (rankTwoToSL2 q (typeAAlgebraGenerator q 1 i t))
  rw [rankTwoToSL2_generator,typeAQuantumCoproduct_generator,quantumCoproduct_generator]
  fin_cases t <;>
    simp [typeACoproductE,typeACoproductF,typeACoproductK,typeACoproductKi,
      coproductE,coproductF,coproductK,coproductKinv,rankTwoToSL2_generator]

end AMSPhysical
#print axioms AMSPhysical.rankTwoToSL2_coproduct
