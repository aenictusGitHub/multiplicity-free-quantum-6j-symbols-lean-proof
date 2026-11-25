import QuantumCupRadialAction
import QuantumCupDiagonalDistinct
import TriangularSimpleSpectrum

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
noncomputable section
namespace AMSPhysical

instance quantumCupIndexLinearOrder (l m c : ℕ) : LinearOrder (QuantumCupIndex l m c) :=
  inferInstanceAs (LinearOrder {t : Fin (m+1) // t.val ≤ l ∧ m-t.val ≤ c})

theorem quantumCupBasis_repr_vector (q : ℝ) (hq : 0<q) (n : ℕ) (hn : 0<n) (l m h c : ℕ)
    (r s : QuantumCupIndex l m c) :
    (quantumCupBasis q hq n hn l m h c).repr (quantumCupVector q n l m h c r) s=if r=s then 1 else 0 := by
  rw [← quantumCupBasis_apply q hq n hn l m h c r,Module.Basis.repr_self,Finsupp.single_apply]

theorem quantumCupLeftAction_triangular (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n) (l m h c : ℕ)
    (i j : QuantumCupIndex l m c) (hij : i<j) :
    (quantumCupBasis q hq n hn l m h c).repr
      (quantumCupLeftAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m h c
        (quantumCupBasis q hq n hn l m h c j)) i=0 := by
  rw [quantumCupBasis_apply,quantumCupLeftAction_vector]
  split_ifs with hs
  · simp only [map_add,map_smul,Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul,quantumCupBasis_repr_vector]
    have hji : j≠i := ne_of_gt hij
    have hri : quantumCupRaiseLeft l m c j hs≠i := by
      intro he
      have hv:=congrArg (fun r : QuantumCupIndex l m c =>r.val.val) he
      change j.val.val+1=i.val.val at hv
      have hh : i.val.val<j.val.val := hij
      omega
    rw [if_neg hji,if_neg hri]
    ring
  · simp only [add_zero,map_smul,Finsupp.smul_apply,smul_eq_mul,quantumCupBasis_repr_vector,if_neg (ne_of_gt hij),mul_zero]

theorem quantumCupLeftAction_diagonal (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n) (l m h c : ℕ)
    (i : QuantumCupIndex l m c) :
    (quantumCupBasis q hq n hn l m h c).repr
      (quantumCupLeftAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m h c
        (quantumCupBasis q hq n hn l m h c i)) i=quantumCupLeftEigenvalue q n l m h i.val.val := by
  rw [quantumCupBasis_apply,quantumCupLeftAction_vector]
  split_ifs with hs
  · simp only [map_add,map_smul,Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul,quantumCupBasis_repr_vector,if_pos rfl,if_true,mul_one]
    have hri : quantumCupRaiseLeft l m c i hs≠i := by
      intro he
      have hv:=congrArg (fun r : QuantumCupIndex l m c =>r.val.val) he
      change i.val.val+1=i.val.val at hv
      omega
    rw [if_neg hri,mul_zero,add_zero]
    exact quantumCupLeftDiagonal_fixed q n l m h i.val.val (by have hi:=i.val.isLt;omega)
  · simp only [add_zero,map_smul,Finsupp.smul_apply,smul_eq_mul,quantumCupBasis_repr_vector,if_pos rfl,if_true,mul_one]
    exact quantumCupLeftDiagonal_fixed q n l m h i.val.val (by have hi:=i.val.isLt;omega)

theorem quantumCupLeftEigenvalue_injective (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n) (l m h c : ℕ) :
    Function.Injective (fun i : QuantumCupIndex l m c =>quantumCupLeftEigenvalue q n l m h i.val.val) := by
  intro i j he
  have hv : i.val.val=j.val.val := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hh|hh
    · have hs:=quantumCupLeftEigenvalue_strict q hq hq1 n hn l m h j.val.val i.val.val hh j.property.1 (by have hj:=j.val.isLt;omega)
      exact (ne_of_lt hs) he
    · have hs:=quantumCupLeftEigenvalue_strict q hq hq1 n hn l m h i.val.val j.val.val hh i.property.1 (by have hi:=i.val.isLt;omega)
      exact (ne_of_gt hs) he
  exact Subtype.ext (Fin.ext hv)

/-- Every admissible first intermediate channel is an actual one-dimensional
eigenspace of the independently constructed physical radial operator. -/
theorem quantumCupLeftAction_eigenspace_finrank (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m h c : ℕ) (i : QuantumCupIndex l m c) :
    Module.finrank ℝ (Module.End.eigenspace (R:=ℝ) (M:=quantumCupSpan q n l m h c)
      (quantumCupLeftAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m h c)
      (quantumCupLeftEigenvalue q n l m h i.val.val))=1 := by
  letI : Module.Finite ℝ (quantumCupSpan q n l m h c) := Module.Finite.of_basis (quantumCupBasis q hq n hn l m h c)
  exact lowerTriangular_eigenspace_finrank (quantumCupBasis q hq n hn l m h c) _ _
    (quantumCupLeftEigenvalue_injective q hq hq1 n hn l m h c)
    (quantumCupLeftAction_triangular q hq hq1 n hn l m h c)
    (quantumCupLeftAction_diagonal q hq hq1 n hn l m h c) i

end AMSPhysical
#print axioms AMSPhysical.quantumCupLeftAction_eigenspace_finrank
