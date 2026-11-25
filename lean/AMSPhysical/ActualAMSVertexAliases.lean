import ActualAMSCoefficientCertificate

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

/-- Native pair realizations and the fixed two-row realization are the
same actual table index. Exterior labels do not survive canonicalization. -/
theorem nativeTypeIITwoRow_fixed_alias (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 2≤n) (a b c d : ℕ) (r : TypeIICommonIndex a b c d) :
    (nativeTypeIITwoRowCarrier q hq hq1 n (by omega) a b c d r).irrep =
      (actualTwoRowCarrier q hq hq1 n (by omega) (a+b) r.val
        (by have hr:=r.isLt;omega)).irrep := by
  apply Subtype.ext
  rfl

/-- The potentially cross-family alias at N=3 is identified as an actual
object, not merely by an equality of dimension or scalar formula. -/
theorem nativeTypeIITwoRow_rank_three_mixed_alias (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (a b c d : ℕ) (r : TypeIICommonIndex a b c d) :
    (nativeTypeIITwoRowCarrier q hq hq1 2 (by omega) a b c d r).irrep =
      (actualMixedCarrier q hq hq1 2 (by omega) (a+b-2*r.val) r.val).irrep := by
  rw [nativeTypeIITwoRow_fixed_alias q hq hq1 2 (by omega)]
  exact actualTwoRow_rank_three_alias q hq hq1 (a+b) r.val (by have hr:=r.isLt;omega)

/-- The actual determinant-defect phase used by the common table has
trivial holonomy along every finite closed path of labelled trees. -/
theorem amsDynkinVertexPhase_closed_path (n : ℕ)
    (path : List (LabelledFusionTree (Fin n → ℤ))) (s : LabelledFusionTree (Fin n → ℤ)) :
    (amsDynkinGlobalSigns n).pathSign s (path++[s])=1 :=
  GlobalVertexSigns.pathSign_closed (amsDynkinGlobalSigns n) path s

end AMSPhysical
#print axioms AMSPhysical.nativeTypeIITwoRow_rank_three_mixed_alias
#print axioms AMSPhysical.amsDynkinVertexPhase_closed_path
