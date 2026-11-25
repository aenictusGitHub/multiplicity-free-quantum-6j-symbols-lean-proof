import QuantumTypeIILeftUnit
import QuantumTypeIIDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical

theorem physicalTypeIILeftCoupling_highestIndependent (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c d : ℕ) (hbal : a+b=c+d) :
    LinearIndependent ℝ (physicalTypeIILeftCoupling q hq hq1 n hn a b c d hbal) := by
  exact bilinear_orthonormal_independent
    (restrictedBilinearPair (physicalTypeIITripleBilin q n a b c)
      (physicalTypeIIHighestSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c d))
    (physicalTypeIILeftCoupling q hq hq1 n hn a b c d hbal)
    (physicalTypeIILeftCoupling_pair q hq hq1 n hn a b c d hbal)

/-- A COMPLETE orthonormal physical Type-II left coupling basis, obtained
from genuine two-row intertwiners and independently proved fusion dimension. -/
def physicalTypeIILeftBasis (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c d : ℕ) (hbal : a+b=c+d) :
    Module.Basis (TypeIICommonIndex a b c d) ℝ
      (physicalTypeIIHighestSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c d) :=
  basisOfLinearIndependentOfCardEqFinrank
    (physicalTypeIILeftCoupling_highestIndependent q hq hq1 n hn a b c d hbal)
    (physicalTypeIIHighest_finrank q hq hq1 n hn a b c d hbal).symm

theorem physicalTypeIILeftBasis_apply (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d) :
    physicalTypeIILeftBasis q hq hq1 n hn a b c d hbal r=
      physicalTypeIILeftCoupling q hq hq1 n hn a b c d hbal r := by
  rw [physicalTypeIILeftBasis,coe_basisOfLinearIndependentOfCardEqFinrank]

end AMSPhysical
#print axioms AMSPhysical.physicalTypeIILeftBasis
