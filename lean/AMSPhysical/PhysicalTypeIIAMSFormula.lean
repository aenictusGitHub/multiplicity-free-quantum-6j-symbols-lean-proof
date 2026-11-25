import TypeIIShiftedRightGauge
import TypeIICertificationGap

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

/-- Complete actual Type-II overlap rank reduction in all ranks and all
admissible labels. The signs belong to whole independent channel families. -/
theorem physicalTypeII_overlap_rank_reduction (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h a b c d:ℕ) (hbal:a+b=c+d):
    ∃ eta:QuantumCupIndex a c b → ℝ,(∀ t,eta t=1 ∨ eta t= -1) ∧
      ∀ r t,physicalTypeIIRecouplingMatrix q hq hq1 (h+1) (by omega) a b c d hbal r t=
        ((-1:ℝ)^r.val*eta t)*quantumRacahMatrix q hq hq1 (a+h) (b+h) c
          (typeIIShiftedLeftPath h a b c d hbal r) (typeIIShiftedRightPath h a b c t) := by
  choose eta heta hV using fun t=>typeIIShiftedUnitEquiv_right q hq hq1 h a b c d hbal t
  refine ⟨eta,heta,?_⟩
  intro r t
  unfold physicalTypeIIRecouplingMatrix
  rw [← typeIIShiftedUnitEquiv_isometry q hq hq1 h a b c d hbal,
    typeIIShiftedUnitEquiv_left,hV t]
  simp only [Submodule.coe_smul_of_tower,map_smul,LinearMap.smul_apply,smul_eq_mul]
  change eta t*(((-1:ℝ)^r.val)*quantumRacahMatrix q hq hq1 (a+h) (b+h) c
    (typeIIShiftedLeftPath h a b c d hbal r) (typeIIShiftedRightPath h a b c t))=_
  ring

/-- AMS Eq. (35), Type II, for the independently defined actual physical
higher-rank Wigner coefficient, at every positive real q different from one,
all ranks and all admissible labels, up to independent vertex/channel signs.
No candidate expression defines the physical coefficient. -/
theorem physicalTypeII_AMS_Eq35 (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h a b c d:ℕ) (hbal:a+b=c+d):
    ∃ eps:TypeIICommonIndex a b c d → ℝ,∃ eta:QuantumCupIndex a c b → ℝ,
      (∀ r,eps r=1 ∨ eps r= -1) ∧ (∀ t,eta t=1 ∨ eta t= -1) ∧
      ∀ r t,physicalTypeIIWignerSymbol q hq hq1 h a b c d hbal r t=
        (eps r*eta t)*(amsFourTrianglePrefactor q h (a:ℤ) b c d
          (typeIILeftLabel a b r.val) (typeIIRightLabel b c t.val.val)*
          AMSGeneral.kernel (quantumFactorialInt q) h true (a:ℤ) b c d
            (typeIILeftLabel a b r.val) (typeIIRightLabel b c t.val.val)) := by
  apply (physicalTypeII_AMS_gauge_iff_overlap q hq hq1 h a b c d hbal).mpr
  obtain ⟨eta,heta,hEq⟩:=physicalTypeII_overlap_rank_reduction q hq hq1 h a b c d hbal
  exact ⟨fun r=>(-1:ℝ)^r.val,eta,fun r=>neg_one_pow_eq_or ℝ r.val,heta,hEq⟩

end AMSPhysical
#print axioms AMSPhysical.physicalTypeII_AMS_Eq35
