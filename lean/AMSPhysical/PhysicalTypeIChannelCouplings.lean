import PhysicalTypeIChannelSpaces
import PhysicalTypeICouplingEigenvectors

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical

def physicalHighestPairing (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n l m h c : ℕ) :
    physicalQuantumHighestMultiplicity q hq hD n l m h c →ₗ[ℝ]
      physicalQuantumHighestMultiplicity q hq hD n l m h c →ₗ[ℝ] ℝ :=
  ((physicalTripleBilin q n l (m+h) c).comp
    (physicalQuantumHighestMultiplicity q hq hD n l m h c).subtype).compl₂
      (physicalQuantumHighestMultiplicity q hq hD n l m h c).subtype

theorem physicalTypeILeftCoupling_mem_channel (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l m h c : ℕ) (hadm : m≤l+c) (hRank : h=0 ∨ n=1) (t : QuantumCupIndex l m c) :
    physicalTypeILeftCoupling q hq hq1 n hn l m h c hadm hRank t∈
      physicalTypeILeftChannelSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m h c t := by
  rw [← completeHighestLeftAction_eigenspace_eq_channel q hq hq1 n hn l m h c hadm hRank]
  exact Module.End.mem_eigenspace_iff.mpr (physicalTypeILeftCoupling_eigen q hq hq1 n hn l m h c hadm hRank t)

theorem physicalTypeIRightCoupling_mem_channel (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l m h c : ℕ) (hadm : m≤l+c) (hRank : h=0 ∨ n=1) (t : QuantumCupIndex l m c) :
    physicalTypeIRightCoupling q hq hq1 n hn l m h c hadm hRank t∈
      physicalTypeIRightChannelSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m h c t := by
  rw [← completeHighestRightAction_eigenspace_eq_channel q hq hq1 n hn l m h c hadm hRank]
  exact Module.End.mem_eigenspace_iff.mpr (physicalTypeIRightCoupling_eigen q hq hq1 n hn l m h c hadm hRank t)

theorem physicalTypeILeftCoupling_unique_sign (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l m h c : ℕ) (hadm : m≤l+c) (hRank : h=0 ∨ n=1) (t : QuantumCupIndex l m c)
    (v : physicalQuantumHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m h c)
    (hv : v∈physicalTypeILeftChannelSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m h c t)
    (hvn : physicalTripleBilin q n l (m+h) c v.val v.val=1) :
    ∃ s : ℝ,(s=1 ∨ s= -1) ∧ v=s • physicalTypeILeftCoupling q hq hq1 n hn l m h c hadm hRank t := by
  rw [← completeHighestLeftAction_eigenspace_eq_channel q hq hq1 n hn l m h c hadm hRank] at hv
  exact unit_eigenvectors_differ_by_sign _ _
    (completeHighestLeftAction_eigenspace_finrank q hq hq1 n hn l m h c hadm hRank t)
    (physicalHighestPairing q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m h c) v _
    (Module.End.mem_eigenspace_iff.mp hv) (physicalTypeILeftCoupling_eigen q hq hq1 n hn l m h c hadm hRank t)
    hvn (physicalTypeILeftCoupling_unit q hq hq1 n hn l m h c hadm hRank t)

theorem physicalTypeIRightCoupling_unique_sign (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l m h c : ℕ) (hadm : m≤l+c) (hRank : h=0 ∨ n=1) (t : QuantumCupIndex l m c)
    (v : physicalQuantumHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m h c)
    (hv : v∈physicalTypeIRightChannelSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m h c t)
    (hvn : physicalTripleBilin q n l (m+h) c v.val v.val=1) :
    ∃ s : ℝ,(s=1 ∨ s= -1) ∧ v=s • physicalTypeIRightCoupling q hq hq1 n hn l m h c hadm hRank t := by
  rw [← completeHighestRightAction_eigenspace_eq_channel q hq hq1 n hn l m h c hadm hRank] at hv
  exact unit_eigenvectors_differ_by_sign _ _
    (completeHighestRightAction_eigenspace_finrank q hq hq1 n hn l m h c hadm hRank t)
    (physicalHighestPairing q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m h c) v _
    (Module.End.mem_eigenspace_iff.mp hv) (physicalTypeIRightCoupling_eigen q hq hq1 n hn l m h c hadm hRank t)
    hvn (physicalTypeIRightCoupling_unit q hq hq1 n hn l m h c hadm hRank t)

end AMSPhysical
#print axioms AMSPhysical.physicalTypeILeftCoupling_mem_channel
#print axioms AMSPhysical.physicalTypeIRightCoupling_unique_sign
