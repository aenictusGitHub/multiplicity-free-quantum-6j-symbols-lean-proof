import QuantumTypeIIHighestBoundaryInjective

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3600000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical

/-- Complete physical highest-space equivalence at the SAME external labels,
characterized by literal boundary coordinates. No metric isometry or AMS
shifted-channel compatibility is claimed by this linear equivalence. -/
def physicalTypeIIUnshiftedBoundaryEquiv (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (a b c d : ℕ) (hbal : a+b=c+d) :
    physicalTypeIIHighestSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c d ≃ₗ[ℝ]
    physicalTypeIIHighestSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) 1 a b c d :=
  (physicalTypeIILeftRawBasis q hq hq1 n hn a b c d hbal).repr.trans
    (physicalTypeIILeftRawBasis q hq hq1 1 (by omega) a b c d hbal).repr.symm

theorem physicalTypeIIUnshiftedBoundaryEquiv_highest (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d) :
    physicalTypeIIUnshiftedBoundaryEquiv q hq hq1 n hn a b c d hbal
      (physicalTypeIILeftHighest q hq hq1 n hn a b c d hbal r)=
      physicalTypeIILeftHighest q hq hq1 1 (by omega) a b c d hbal r := by
  rw [← physicalTypeIILeftRawBasis_apply q hq hq1 n hn a b c d hbal r,
    ← physicalTypeIILeftRawBasis_apply q hq hq1 1 (by omega) a b c d hbal r]
  apply (physicalTypeIILeftRawBasis q hq hq1 1 (by omega) a b c d hbal).repr.injective
  unfold physicalTypeIIUnshiftedBoundaryEquiv
  simp only [LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply,Module.Basis.repr_self]

theorem physicalTypeIIUnshiftedBoundaryEquiv_coordinates (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (a b c d : ℕ) (hbal : a+b=c+d)
    (v : physicalTypeIIHighestSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c d) :
    physicalTypeIIHighestBoundaryMap q hq hq1 n hn a b c d v=
      physicalTypeIIHighestBoundaryMap q hq hq1 1 (by omega) a b c d
        (physicalTypeIIUnshiftedBoundaryEquiv q hq hq1 n hn a b c d hbal v) := by
  have he : physicalTypeIIHighestBoundaryMap q hq hq1 n hn a b c d=
      (physicalTypeIIHighestBoundaryMap q hq hq1 1 (by omega) a b c d).comp
        (physicalTypeIIUnshiftedBoundaryEquiv q hq hq1 n hn a b c d hbal).toLinearMap := by
    apply (physicalTypeIILeftRawBasis q hq hq1 n hn a b c d hbal).ext
    intro r
    rw [physicalTypeIILeftRawBasis_apply]
    change twoVertexTripleProjection n hn a b c
      (physicalTypeIILeftHighest q hq hq1 n hn a b c d hbal r).val=
      twoVertexTripleProjection 1 (by omega) a b c
        (physicalTypeIIUnshiftedBoundaryEquiv q hq hq1 n hn a b c d hbal
          (physicalTypeIILeftHighest q hq hq1 n hn a b c d hbal r)).val
    rw [physicalTypeIIUnshiftedBoundaryEquiv_highest,physicalTypeIILeftHighest_boundary,physicalTypeIILeftHighest_boundary]
  exact DFunLike.congr_fun he v

end AMSPhysical
#print axioms AMSPhysical.physicalTypeIIUnshiftedBoundaryEquiv_coordinates
