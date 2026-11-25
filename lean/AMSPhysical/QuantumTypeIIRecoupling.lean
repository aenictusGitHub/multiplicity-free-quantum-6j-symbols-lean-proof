import QuantumTypeIILeftBasis
import QuantumTypeIIRightBasis
import OrthonormalBasisChange

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical

/-- Actual arbitrary-rank physical Type-II recoupling matrix. Both vectors
are independently constructed physical unit channel couplings; no AMS sum
occurs in this definition. -/
def physicalTypeIIRecouplingMatrix (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c d : ℕ) (hbal : a+b=c+d) : Matrix (TypeIICommonIndex a b c d) (QuantumCupIndex a c b) ℝ :=
  fun r t =>physicalTypeIITripleBilin q n a b c
    (physicalTypeIILeftCoupling q hq hq1 n hn a b c d hbal r).val
    (physicalTypeIIRightCoupling q hq hq1 n hn a b c d hbal t).val

theorem physicalTypeIIRecoupling_rows (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c d : ℕ) (hbal : a+b=c+d) (i j : TypeIICommonIndex a b c d) :
    (∑ k,physicalTypeIIRecouplingMatrix q hq hq1 n hn a b c d hbal i k*physicalTypeIIRecouplingMatrix q hq hq1 n hn a b c d hbal j k)=if i=j then 1 else 0 := by
  let B:=restrictedBilinearPair (physicalTypeIITripleBilin q n a b c)
    (physicalTypeIIHighestSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c d)
  have hb (r s : TypeIICommonIndex a b c d) :
      B (physicalTypeIILeftBasis q hq hq1 n hn a b c d hbal r)
        (physicalTypeIILeftBasis q hq hq1 n hn a b c d hbal s)=if r=s then 1 else 0 := by
    simp only [physicalTypeIILeftBasis_apply]
    exact physicalTypeIILeftCoupling_pair q hq hq1 n hn a b c d hbal r s
  have hc (r s : QuantumCupIndex a c b) :
      B (physicalTypeIIRightBasis q hq hq1 n hn a b c d hbal r)
        (physicalTypeIIRightBasis q hq hq1 n hn a b c d hbal s)=if r=s then 1 else 0 := by
    simp only [physicalTypeIIRightBasis_apply]
    exact physicalTypeIIRightCoupling_pair q hq hq1 n hn a b c d hbal r s
  have he:=orthonormal_basis_change_rows B
    (physicalTypeIILeftBasis q hq hq1 n hn a b c d hbal)
    (physicalTypeIIRightBasis q hq hq1 n hn a b c d hbal) hb hc i j
  simpa only [physicalTypeIILeftBasis_apply,physicalTypeIIRightBasis_apply,physicalTypeIIRecouplingMatrix] using he

theorem physicalTypeIIRecoupling_cols (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c d : ℕ) (hbal : a+b=c+d) (i j : QuantumCupIndex a c b) :
    (∑ k,physicalTypeIIRecouplingMatrix q hq hq1 n hn a b c d hbal k i*physicalTypeIIRecouplingMatrix q hq hq1 n hn a b c d hbal k j)=if i=j then 1 else 0 := by
  let B:=restrictedBilinearPair (physicalTypeIITripleBilin q n a b c)
    (physicalTypeIIHighestSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c d)
  have hb (r s : TypeIICommonIndex a b c d) :
      B (physicalTypeIILeftBasis q hq hq1 n hn a b c d hbal r)
        (physicalTypeIILeftBasis q hq hq1 n hn a b c d hbal s)=if r=s then 1 else 0 := by
    simp only [physicalTypeIILeftBasis_apply]
    exact physicalTypeIILeftCoupling_pair q hq hq1 n hn a b c d hbal r s
  have hc (r s : QuantumCupIndex a c b) :
      B (physicalTypeIIRightBasis q hq hq1 n hn a b c d hbal r)
        (physicalTypeIIRightBasis q hq hq1 n hn a b c d hbal s)=if r=s then 1 else 0 := by
    simp only [physicalTypeIIRightBasis_apply]
    exact physicalTypeIIRightCoupling_pair q hq hq1 n hn a b c d hbal r s
  have he:=orthonormal_basis_change_cols B
    (physicalTypeIILeftBasis q hq hq1 n hn a b c d hbal)
    (physicalTypeIIRightBasis q hq hq1 n hn a b c d hbal) hb hc i j
  simpa only [physicalTypeIILeftBasis_apply,physicalTypeIIRightBasis_apply,physicalTypeIIRecouplingMatrix] using he

theorem physicalTypeIIRecoupling_mul_transpose (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c d : ℕ) (hbal : a+b=c+d) :
    let M:=physicalTypeIIRecouplingMatrix q hq hq1 n hn a b c d hbal
    M*M.transpose=(1 : Matrix (TypeIICommonIndex a b c d) (TypeIICommonIndex a b c d) ℝ) := by
  ext i j
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply]
  exact physicalTypeIIRecoupling_rows q hq hq1 n hn a b c d hbal i j

theorem physicalTypeIIRecoupling_transpose_mul (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c d : ℕ) (hbal : a+b=c+d) :
    let M:=physicalTypeIIRecouplingMatrix q hq hq1 n hn a b c d hbal
    M.transpose*M=(1 : Matrix (QuantumCupIndex a c b) (QuantumCupIndex a c b) ℝ) := by
  ext i j
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply]
  exact physicalTypeIIRecoupling_cols q hq hq1 n hn a b c d hbal i j

end AMSPhysical
#print axioms AMSPhysical.physicalTypeIIRecoupling_mul_transpose
#print axioms AMSPhysical.physicalTypeIIRecoupling_transpose_mul
