import QuantumTypeIIBoundaryEquivalence
import QuantumTypeIIRecoupling

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 700000
noncomputable section
namespace AMSPhysical

/-- An actual Type-II overlap is the coordinate in the independently
constructed complete unit left basis. -/
theorem physicalTypeIIRecoupling_unit_coordinate (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (a b c d : ℕ) (hbal : a+b=c+d)
    (r : TypeIICommonIndex a b c d) (t : QuantumCupIndex a c b) :
    physicalTypeIIRecouplingMatrix q hq hq1 n hn a b c d hbal r t=
      (physicalTypeIILeftBasis q hq hq1 n hn a b c d hbal).repr
        (physicalTypeIIRightCoupling q hq hq1 n hn a b c d hbal t) r := by
  let B:=restrictedBilinearPair (physicalTypeIITripleBilin q n a b c)
    (physicalTypeIIHighestSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c d)
  have hb (r s : TypeIICommonIndex a b c d) :
      B (physicalTypeIILeftBasis q hq hq1 n hn a b c d hbal r)
        (physicalTypeIILeftBasis q hq hq1 n hn a b c d hbal s)=if r=s then 1 else 0 := by
    simp only [physicalTypeIILeftBasis_apply]
    exact physicalTypeIILeftCoupling_pair q hq hq1 n hn a b c d hbal r s
  have he:=orthonormal_basis_coord_right B (physicalTypeIILeftBasis q hq hq1 n hn a b c d hbal)
    hb r (physicalTypeIIRightCoupling q hq hq1 n hn a b c d hbal t)
  simpa only [physicalTypeIILeftBasis_apply,physicalTypeIIRecouplingMatrix] using he

/-- The only factor between raw two-row boundary coordinates and physical
unit overlap is the square root of the ACTUAL positive left-tree norm. -/
theorem physicalTypeIIRecoupling_raw_coordinate (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (a b c d : ℕ) (hbal : a+b=c+d)
    (r : TypeIICommonIndex a b c d) (t : QuantumCupIndex a c b) :
    physicalTypeIIRecouplingMatrix q hq hq1 n hn a b c d hbal r t=
      Real.sqrt (physicalTypeIILeftHighestNormSq q hq hq1 n hn a b c d hbal r)*
        (physicalTypeIILeftRawBasis q hq hq1 n hn a b c d hbal).repr
          (physicalTypeIIRightCoupling q hq hq1 n hn a b c d hbal t) r := by
  rw [physicalTypeIILeftRawBasis,Module.Basis.repr_unitsSMul,physicalTypeIIRecoupling_unit_coordinate]
  simp only [Units.smul_def,Units.val_inv_eq_inv_val,Units.val_mk0,smul_eq_mul]
  have hs:Real.sqrt (physicalTypeIILeftHighestNormSq q hq hq1 n hn a b c d hbal r)≠0:=
    ne_of_gt (Real.sqrt_pos.mpr (physicalTypeIILeftHighest_norm_pos q hq hq1 n hn a b c d hbal r))
  rw [← mul_assoc,mul_inv_cancel₀ hs,one_mul]

/-- Complete reduction of an actual higher-rank Type-II overlap to the
same-label rank-two RAW coordinate of its literal boundary restriction.
No shifted-label metric or right-channel identification is asserted. -/
theorem physicalTypeIIRecoupling_unshifted_boundary_coordinate (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (a b c d : ℕ) (hbal : a+b=c+d)
    (r : TypeIICommonIndex a b c d) (t : QuantumCupIndex a c b) :
    physicalTypeIIRecouplingMatrix q hq hq1 n hn a b c d hbal r t=
      Real.sqrt (physicalTypeIILeftHighestNormSq q hq hq1 n hn a b c d hbal r)*
        (physicalTypeIILeftRawBasis q hq hq1 1 (by omega) a b c d hbal).repr
          (physicalTypeIIUnshiftedBoundaryEquiv q hq hq1 n hn a b c d hbal
            (physicalTypeIIRightCoupling q hq hq1 n hn a b c d hbal t)) r := by
  rw [physicalTypeIIRecoupling_raw_coordinate]
  unfold physicalTypeIIUnshiftedBoundaryEquiv
  simp only [LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply]

end AMSPhysical
#print axioms AMSPhysical.physicalTypeIIRecoupling_unshifted_boundary_coordinate
