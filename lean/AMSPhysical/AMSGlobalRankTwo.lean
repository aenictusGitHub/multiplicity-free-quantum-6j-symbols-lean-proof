import GlobalSL2Vertices
import PhysicalTypeIOverlapNormalization
import PhysicalTypeIIOverlapNormalization

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

/-- At N=2, all Type-I physical overlaps are realized by the SAME global
actual trivalent CG family, simultaneously for every admissible quadruple. -/
theorem physicalTypeI_global_vertices_rank_two (q : ℝ) (hq : 0 < q) (hq1 : q ≠ 1)
    (l m c : ℕ) (hadm : m ≤ l+c) (s t : QuantumCupIndex l m c) :
    physicalTripleBilin q 1 l m c
      (physicalTypeILeftCoupling q hq hq1 1 (by omega) l m 0 c hadm (Or.inl rfl) s).val
      (physicalTypeIRightCoupling q hq hq1 1 (by omega) l m 0 c hadm (Or.inl rfl) t).val =
    globalSL2Recoupling q hq hq1 l m c
      (quantumCupLeftPath l m 0 c s) (quantumCupRightPath l m 0 c t) := by
  simpa only [Nat.add_zero, Nat.add_sub_cancel, globalSL2Recoupling_eq] using
    physicalTypeICoupling_overlap_rankTwo q hq hq1 1 (by omega) l m 0 c hadm (Or.inl rfl) s t

/-- The same global CG family, with no extra Type-II vertex table or
quadruple-dependent vertex parameters, realizes all Type-II overlaps at N=2. -/
theorem physicalTypeII_global_vertices_rank_two (q : ℝ) (hq : 0 < q) (hq1 : q ≠ 1)
    (a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d)
    (t : QuantumCupIndex a c b) :
    physicalTypeIITripleBilin q 1 a b c
      (physicalTypeIICalibratedLeft q hq hq1 0 a b c d hbal r).val
      (physicalTypeIICalibratedRight q hq hq1 0 a b c d hbal t).val =
    globalSL2Recoupling q hq hq1 a b c
      (typeIIShiftedLeftPath 0 a b c d hbal r) (typeIIShiftedRightPath 0 a b c t) := by
  rw [← typeIIShiftedUnitEquiv_isometry q hq hq1 0 a b c d hbal,
    physicalTypeIICalibratedLeft_standard, physicalTypeIICalibratedRight_standard]
  rfl

end AMSPhysical
#print axioms AMSPhysical.physicalTypeI_global_vertices_rank_two
#print axioms AMSPhysical.physicalTypeII_global_vertices_rank_two
