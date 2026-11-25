import QuantumTypeADynkinReflection
import QuantumTypeAChevalley

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical
variable {K : Type*} [Field K]

theorem typeADynkinReflection_chevalley (q : K) (hq : q≠0) (n : ℕ) :
    (typeADynkinReflection q n).comp (typeAChevalley q hq n)=
      (typeAChevalley q hq n).comp (typeADynkinReflection q n) := by
  apply RingQuot.ringQuot_ext'
  apply FreeAlgebra.hom_ext
  funext it
  obtain ⟨i,t⟩ := it
  change typeADynkinReflection q n (typeAChevalley q hq n (typeAAlgebraGenerator q n i t))=
    typeAChevalley q hq n (typeADynkinReflection q n (typeAAlgebraGenerator q n i t))
  fin_cases t <;> simp [typeADynkinReflection_generator,typeAChevalley_generator]

end AMSPhysical
