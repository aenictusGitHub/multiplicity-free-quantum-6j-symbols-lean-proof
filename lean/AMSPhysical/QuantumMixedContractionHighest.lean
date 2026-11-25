import QuantumMixedContraction
import QuantumMixedCreationHighest
import QuantumMixedFusionNorm
import QuantumMixedNormalization

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

/-- The physical contraction coefficient is determined by its actual metric
adjunction and the independently evaluated highest-vector norms. -/
theorem mixedFiniteContraction_highest (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l m : ℕ) (r : MixedFusionIndex l m) :
    mixedFiniteContraction q hq n l m
        (mixedFusionHighestAt q n (l+1) (m+1) (mixedFusionIndexSucc l m r))=
      (q^(-(l:ℤ)-(r.val:ℤ))*mixedCouplingNormClosed q n (l-r.val) (m-r.val) (r.val+1)/
        mixedCouplingNormClosed q n (l-r.val) (m-r.val) r.val) • mixedFusionHighestAt q n l m r := by
  let v := mixedFusionHighestAt q n l m r
  let w := mixedFusionHighestAt q n (l+1) (m+1) (mixedFusionIndexSucc l m r)
  let a := mixedBoundaryFunctional n l m r (mixedFiniteContraction q hq n l m w)
  have hu : mixedFiniteContraction q hq n l m w=a • v := by
    apply mixedFusionHighestAt_full_weight_unique q hq hq1 n hn l m r
    · intro i
      rw [← mixedFiniteContraction_intertwines q hq hq1 n l m]
      change mixedFiniteContraction q hq n l m
        (typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n (l+1) (m+1)
          (typeAAlgebraGenerator q n i 0) (mixedFusionHighestAt q n (l+1) (m+1) (mixedFusionIndexSucc l m r)))=0
      rw [mixedFusionHighestAt_E_zero q hq hq1,map_zero]
    · intro i
      rw [← mixedFiniteContraction_intertwines q hq hq1 n l m]
      change mixedFiniteContraction q hq n l m
        (typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n (l+1) (m+1)
          (typeAAlgebraGenerator q n i 2) (mixedFusionHighestAt q n (l+1) (m+1) (mixedFusionIndexSucc l m r)))=_
      rw [mixedFusionHighestAt_K,map_smul]
      simp only [w,mixedFusionIndexSucc,Nat.add_sub_add_right]
  have he := mixedFiniteContraction_adjoint q hq n l m v w
  change mixedTensorBilin q n (l+1) (m+1)
      (mixedFiniteCreation q n l m (mixedFusionHighestAt q n l m r)) w=_ at he
  rw [mixedFiniteCreation_highest q hq hq1 n hn,hu] at he
  simp only [map_smul,LinearMap.smul_apply,smul_eq_mul] at he
  change q^(-(l:ℤ)-(r.val:ℤ))*mixedTensorBilin q n (l+1) (m+1)
      (mixedFusionHighestAt q n (l+1) (m+1) (mixedFusionIndexSucc l m r))
      (mixedFusionHighestAt q n (l+1) (m+1) (mixedFusionIndexSucc l m r))=
    a*mixedTensorBilin q n l m (mixedFusionHighestAt q n l m r) (mixedFusionHighestAt q n l m r) at he
  rw [mixedFusionHighestAt_norm_closed q hq n hn,mixedFusionHighestAt_norm_closed q hq n hn] at he
  simp only [mixedFusionIndexSucc,Nat.add_sub_add_right] at he
  have ha : a=q^(-(l:ℤ)-(r.val:ℤ))*mixedCouplingNormClosed q n (l-r.val) (m-r.val) (r.val+1)/
      mixedCouplingNormClosed q n (l-r.val) (m-r.val) r.val := by
    apply (eq_div_iff (ne_of_gt (mixedCouplingNormClosed_pos q hq n (l-r.val) (m-r.val) r.val))).mpr
    exact he.symm
  exact hu.trans (congrArg (fun c : ℝ =>c • v) ha)

end AMSPhysical
#print axioms AMSPhysical.mixedFiniteContraction_highest
