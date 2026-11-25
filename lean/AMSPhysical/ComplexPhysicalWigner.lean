import ComplexRacahAnalytic
import ComplexWeylDimensions
import PhysicalTypeIOverlapNormalization
import PhysicalTypeIIOverlapNormalization
import PhysicalTypeIIExactAMS

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

/-- Concrete complex continuation built from independent finite CG-tree
overlaps and actual higher-rank Weyl dimensions, without an AMS expression. -/
def complexPhysicalTypeIWigner (q:ℂ) (h l m c:ℕ) (s t:QuantumCupIndex l m c):ℂ:=
  (-1:ℂ)^(l+c)*complexRacahOverlap q l (m+h) c
    (quantumCupLeftPath l m h c s) (quantumCupRightPath l m h c t)/
      complexPositiveRoot (complexMixedWeyl q h (l-s.val.val) (m-s.val.val)*
        complexMixedWeyl q h (c-(m-t.val.val)) t.val.val)

def complexPhysicalTypeIIWigner (q:ℂ) (h a b c d:ℕ) (hbal:a+b=c+d)
    (r:TypeIICommonIndex a b c d) (t:QuantumCupIndex a c b):ℂ:=
  (-1:ℂ)^(a+b)*complexRacahOverlap q (a+h) (b+h) c
    (typeIIShiftedLeftPath h a b c d hbal r) (typeIIShiftedRightPath h a b c t)/
      complexPositiveRoot (complexSameWeyl q h (a-r.val) (b-r.val) r.val*
        complexMixedWeyl q h (b-(c-t.val.val)) t.val.val)

theorem complexPhysicalTypeIWigner_ofReal_actual (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h l m c:ℕ) (hadm:m≤l+c) (s t:QuantumCupIndex l m c):
    complexPhysicalTypeIWigner (q:ℂ) h l m c s t=
      (physicalTypeIWignerSymbol q hq hq1 h l m c hadm s t:ℂ):=by
  rw [physicalTypeIWigner_overlap_normalization q hq hq1]
  unfold complexPhysicalTypeIWigner
  rw [complexRacahOverlap_ofReal_actual q hq hq1,complexMixedWeyl_ofReal,complexMixedWeyl_ofReal,
    ← Complex.ofReal_mul,complexPositiveRoot_ofReal _
      (mul_pos (mixedWeyl_quantum_pos q hq h (l-s.val.val) (m-s.val.val))
        (mixedWeyl_quantum_pos q hq h (c-(m-t.val.val)) t.val.val))]
  simp only [Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_neg,Complex.ofReal_one]

theorem complexPhysicalTypeIIWigner_ofReal_actual (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h a b c d:ℕ) (hbal:a+b=c+d) (r:TypeIICommonIndex a b c d) (t:QuantumCupIndex a c b):
    complexPhysicalTypeIIWigner (q:ℂ) h a b c d hbal r t=
      (physicalTypeIICalibratedWignerSymbol q hq hq1 h a b c d hbal r t:ℂ):=by
  unfold complexPhysicalTypeIIWigner physicalTypeIICalibratedWignerSymbol
  rw [← sameWeyl_actual_dimension q hq hq1 h (a-r.val) (b-r.val) r.val,
    ← mixedWeyl_actual_dimension q hq hq1 h (b-(c-t.val.val)) t.val.val,
    physicalTypeIICalibrated_overlap_normalization q hq hq1,
    complexRacahOverlap_ofReal_actual q hq hq1,complexSameWeyl_ofReal,complexMixedWeyl_ofReal,
    ← Complex.ofReal_mul,complexPositiveRoot_ofReal _
      (mul_pos (sameWeyl_quantum_pos q hq h (a-r.val) (b-r.val) r.val)
        (mixedWeyl_quantum_pos q hq h (b-(c-t.val.val)) t.val.val))]
  simp only [Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_neg,Complex.ofReal_one]

end AMSPhysical
#print axioms AMSPhysical.complexPhysicalTypeIWigner_ofReal_actual
#print axioms AMSPhysical.complexPhysicalTypeIIWigner_ofReal_actual
