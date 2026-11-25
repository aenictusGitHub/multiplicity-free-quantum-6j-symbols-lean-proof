import QuantumCupSimpleSpectrum

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
noncomputable section
namespace AMSPhysical

theorem quantumCupRightAction_triangular (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n) (l m h c : ℕ)
    (i j : QuantumCupIndex l m c) (hij : j < i) :
    (quantumCupBasis q hq n hn l m h c).repr
      (quantumCupRightAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m h c
        (quantumCupBasis q hq n hn l m h c j)) i=0 := by
  rw [quantumCupBasis_apply,quantumCupRightAction_vector]
  split_ifs with hs
  · simp only [map_add,map_smul,Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul,quantumCupBasis_repr_vector]
    have hji : j≠i := ne_of_lt hij
    have hri : quantumCupRaiseRight l m c j hs≠i := by
      intro he
      have hv:=congrArg (fun r : QuantumCupIndex l m c =>r.val.val) he
      change j.val.val-1=i.val.val at hv
      have hh : j.val.val < i.val.val := hij
      omega
    rw [if_neg hji,if_neg hri]
    ring
  · simp only [add_zero,map_smul,Finsupp.smul_apply,smul_eq_mul,quantumCupBasis_repr_vector,if_neg (ne_of_lt hij),mul_zero]

theorem quantumCupRightAction_diagonal (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n) (l m h c : ℕ)
    (i : QuantumCupIndex l m c) :
    (quantumCupBasis q hq n hn l m h c).repr
      (quantumCupRightAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m h c
        (quantumCupBasis q hq n hn l m h c i)) i=quantumCupLeftEigenvalue q n c m h (m-i.val.val) := by
  have hfixed : quantumCupLeftDiagonal q n (c:ℤ) (h:ℤ) (m-i.val.val) i.val.val=
      quantumCupLeftEigenvalue q n c m h (m-i.val.val) := by
    simpa only [Nat.sub_sub_self (by have hi:=i.val.isLt;omega : i.val.val≤m)] using
      quantumCupLeftDiagonal_fixed q n c m h (m-i.val.val) (by omega)
  rw [quantumCupBasis_apply,quantumCupRightAction_vector]
  split_ifs with hs
  · simp only [map_add,map_smul,Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul,quantumCupBasis_repr_vector,if_pos rfl,if_true,mul_one]
    have hri : quantumCupRaiseRight l m c i hs≠i := by
      intro he
      have hv:=congrArg (fun r : QuantumCupIndex l m c =>r.val.val) he
      change i.val.val-1=i.val.val at hv
      have hh:=hs.1
      omega
    rw [if_neg hri,mul_zero,add_zero]
    exact hfixed
  · simp only [add_zero,map_smul,Finsupp.smul_apply,smul_eq_mul,quantumCupBasis_repr_vector,if_pos rfl,if_true,mul_one]
    exact hfixed

theorem quantumCupRightEigenvalue_injective (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n) (l m h c : ℕ) :
    Function.Injective (fun i : QuantumCupIndex l m c =>quantumCupLeftEigenvalue q n c m h (m-i.val.val)) := by
  intro i j he
  have hv : m-i.val.val=m-j.val.val := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hh|hh
    · have hs:=quantumCupLeftEigenvalue_strict q hq hq1 n hn c m h (m-j.val.val) (m-i.val.val) hh j.property.2 (by omega)
      exact (ne_of_lt hs) he
    · have hs:=quantumCupLeftEigenvalue_strict q hq hq1 n hn c m h (m-i.val.val) (m-j.val.val) hh i.property.2 (by omega)
      exact (ne_of_gt hs) he
  apply Subtype.ext
  apply Fin.ext
  have hi:=i.val.isLt
  have hj:=j.val.isLt
  omega

theorem quantumCupRightAction_eigenspace_finrank (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m h c : ℕ) (i : QuantumCupIndex l m c) :
    Module.finrank ℝ (Module.End.eigenspace (R:=ℝ) (M:=quantumCupSpan q n l m h c)
      (quantumCupRightAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m h c)
      (quantumCupLeftEigenvalue q n c m h (m-i.val.val)))=1 := by
  letI : Module.Finite ℝ (quantumCupSpan q n l m h c) := Module.Finite.of_basis (quantumCupBasis q hq n hn l m h c)
  exact upperTriangular_eigenspace_finrank (quantumCupBasis q hq n hn l m h c) _ _
    (quantumCupRightEigenvalue_injective q hq hq1 n hn l m h c)
    (quantumCupRightAction_triangular q hq hq1 n hn l m h c)
    (quantumCupRightAction_diagonal q hq hq1 n hn l m h c) i

end AMSPhysical
#print axioms AMSPhysical.quantumCupRightAction_eigenspace_finrank
