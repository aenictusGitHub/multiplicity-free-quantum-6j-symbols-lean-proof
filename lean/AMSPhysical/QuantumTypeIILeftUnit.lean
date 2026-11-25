import QuantumTypeIILeftOrthogonal
import BilinearOrthonormal

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical

def physicalTypeIILeftHighestNormSq (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d) : ℝ :=
  physicalTypeIITripleBilin q n a b c
    (physicalTypeIILeftHighest q hq hq1 n hn a b c d hbal r).val
    (physicalTypeIILeftHighest q hq hq1 n hn a b c d hbal r).val

/-- A unit vector on the independently constructed physical Type-II left
coupling line, normalized by its actual positive compact norm. -/
def physicalTypeIILeftCoupling (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d) :
    physicalTypeIIHighestSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c d :=
  (Real.sqrt (physicalTypeIILeftHighestNormSq q hq hq1 n hn a b c d hbal r))⁻¹ •
    physicalTypeIILeftHighest q hq hq1 n hn a b c d hbal r

theorem physicalTypeIILeftCoupling_norm_one (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d) :
    physicalTypeIITripleBilin q n a b c
      (physicalTypeIILeftCoupling q hq hq1 n hn a b c d hbal r).val
      (physicalTypeIILeftCoupling q hq hq1 n hn a b c d hbal r).val=1 := by
  unfold physicalTypeIILeftCoupling
  simp only [Submodule.coe_smul_of_tower,map_smul,LinearMap.smul_apply,smul_eq_mul]
  have hp:=physicalTypeIILeftHighest_norm_pos q hq hq1 n hn a b c d hbal r
  change 0<physicalTypeIILeftHighestNormSq q hq hq1 n hn a b c d hbal r at hp
  change (Real.sqrt (physicalTypeIILeftHighestNormSq q hq hq1 n hn a b c d hbal r))⁻¹*
    ((Real.sqrt (physicalTypeIILeftHighestNormSq q hq hq1 n hn a b c d hbal r))⁻¹*
      physicalTypeIILeftHighestNormSq q hq hq1 n hn a b c d hbal r)=1
  have hs:=Real.sq_sqrt hp.le
  have hs0:=ne_of_gt (Real.sqrt_pos.mpr hp)
  field_simp [hs0]
  nlinarith

theorem physicalTypeIILeftCoupling_mem (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d) :
    (physicalTypeIILeftCoupling q hq hq1 n hn a b c d hbal r).val∈
      physicalTypeIILeftChannel q hq hq1 n hn a b c d r := by
  exact Submodule.smul_mem _ _ (physicalTypeIILeftHighest_mem q hq hq1 n hn a b c d hbal r)

theorem physicalTypeIILeftCoupling_pair (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c d : ℕ) (hbal : a+b=c+d) (r s : TypeIICommonIndex a b c d) :
    physicalTypeIITripleBilin q n a b c
      (physicalTypeIILeftCoupling q hq hq1 n hn a b c d hbal r).val
      (physicalTypeIILeftCoupling q hq hq1 n hn a b c d hbal s).val=if r=s then 1 else 0 := by
  split_ifs with he
  · subst s
    exact physicalTypeIILeftCoupling_norm_one q hq hq1 n hn a b c d hbal r
  · exact physicalTypeIILeftChannels_orthogonal q hq hq1 n hn a b c d r s he _ _
      (physicalTypeIILeftCoupling_mem q hq hq1 n hn a b c d hbal r)
      (physicalTypeIILeftCoupling_mem q hq hq1 n hn a b c d hbal s)

theorem physicalTypeIILeftCoupling_linearIndependent (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c d : ℕ) (hbal : a+b=c+d) :
    LinearIndependent ℝ (fun r : TypeIICommonIndex a b c d =>
      (physicalTypeIILeftCoupling q hq hq1 n hn a b c d hbal r).val) :=
  bilinear_orthonormal_independent (physicalTypeIITripleBilin q n a b c) _
    (physicalTypeIILeftCoupling_pair q hq hq1 n hn a b c d hbal)

end AMSPhysical
#print axioms AMSPhysical.physicalTypeIILeftCoupling_linearIndependent
