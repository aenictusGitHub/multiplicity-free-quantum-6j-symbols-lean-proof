import ActualAMSVertexAliases

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace AMSPhysical

/-- Complete shared actual vertex certificate for both AMS families at
N=h+2>=3, q>0, q!=1. The table is fixed before all exterior/channel labels.
Every admissible entry is a full isometric intertwiner. Both coefficients
are defined by compositions of this same table and actual pivotal dimensions. -/
theorem AMS_Eq35_shared_actual_vertex_certificate (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h : ℕ) (hh : 1≤h) :
    SharedActualAMSVertexTableSpec q hq hq1 h (amsActualVertexTable q hq hq1 (h+1) (by omega)) ∧
    (∀ A B C,ActualAMSVertex q hq hq1 h A B C →
      ActualUnitaryVertex (ne_of_gt hq) A B C (amsActualVertexTable q hq hq1 (h+1) (by omega) A B C)) ∧
    (∀ (l m c : ℕ) (_hadm : m≤l+c) (s t : QuantumCupIndex l m c),
      actualTypeIWignerSymbol q hq hq1 h hh l m c s t=
        amsFourTrianglePrefactor q h (l:ℤ) m c (l+c-m)
          (typeILeftLabel l m s.val.val) (typeIRightLabel m c t.val.val)*
        AMSGeneral.kernel (quantumFactorialInt q) h false (l:ℤ) m c (l+c-m)
          (typeILeftLabel l m s.val.val) (typeIRightLabel m c t.val.val)) ∧
    (∀ (a b c d : ℕ) (_hbal : a+b=c+d)
        (r : TypeIICommonIndex a b c d) (t : QuantumCupIndex a c b),
      actualTypeIIWignerSymbol q hq hq1 h hh a b c d r t=
        amsFourTrianglePrefactor q h (a:ℤ) b c d
          (typeIILeftLabel a b r.val) (typeIIRightLabel b c t.val.val)*
        AMSGeneral.kernel (quantumFactorialInt q) h true (a:ℤ) b c d
          (typeIILeftLabel a b r.val) (typeIIRightLabel b c t.val.val)) :=
  ⟨amsActualVertexTable_shared q hq hq1 h hh,
    amsActualVertexTable_unitary q hq hq1 h hh,
    actualTypeI_AMS_Eq35_shared_vertices q hq hq1 h hh,
    actualTypeII_AMS_Eq35_shared_vertices q hq hq1 h hh⟩

end AMSPhysical
#print axioms AMSPhysical.AMS_Eq35_shared_actual_vertex_certificate
