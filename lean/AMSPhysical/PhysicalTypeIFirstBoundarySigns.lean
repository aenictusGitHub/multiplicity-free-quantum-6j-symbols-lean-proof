import PhysicalTypeIFirstBoundaryTransport
import StandardCupFirstBoundarySigns
import PhysicalTypeIChannelCouplings

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

def typeIFirstBoundarySign (n m t : ℕ) : ℝ := quantumCupRankGauge n m*(-1:ℝ)^(m-t)

theorem typeIFirstBoundarySign_square (n m t : ℕ) :
    typeIFirstBoundarySign n m t * typeIFirstBoundarySign n m t=1 := by
  unfold typeIFirstBoundarySign quantumCupRankGauge
  rw [← pow_add,← mul_pow]
  norm_num

theorem physicalTypeIRightCoupling_first_boundary_signed_pos (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m h c : ℕ) (hadm : m≤l+c) (hRank : h=0 ∨ n=1)
    (t : QuantumCupIndex l m c) :
    0 < typeIFirstBoundarySign n m t.val.val * physicalTypeIFirstBoundary n l m h c
      (physicalTypeIRightCoupling q hq hq1 n hn l m h c hadm hRank t).val := by
  have hp:=standardCupRightHighest_first_boundary_signed_pos q hq hq1 l m (h+n-1) c hadm t
  rw [physicalTypeIRightCoupling_first_boundary_transport q hq hq1 n hn l m h c hadm hRank] at hp
  have hnrm:=quantumCupRankNormalization_pos q hq n hn l m h c hadm
  have he : (-1:ℝ)^(m-t.val.val)*(quantumCupRankNormalization q hq n hn l m h c hadm *
      quantumCupRankGauge n m * physicalTypeIFirstBoundary n l m h c
        (physicalTypeIRightCoupling q hq hq1 n hn l m h c hadm hRank t).val) =
      quantumCupRankNormalization q hq n hn l m h c hadm *
        (typeIFirstBoundarySign n m t.val.val * physicalTypeIFirstBoundary n l m h c
          (physicalTypeIRightCoupling q hq hq1 n hn l m h c hadm hRank t).val) := by
    unfold typeIFirstBoundarySign
    ring
  rw [he] at hp
  exact (mul_pos_iff_of_pos_left hnrm).mp hp

theorem physicalTypeILeftCoupling_first_boundary_signed_pos (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m h c : ℕ) (hadm : m≤l+c) (hRank : h=0 ∨ n=1)
    (t : QuantumCupIndex l m c) :
    0 < typeIFirstBoundarySign n m t.val.val * physicalTypeIFirstBoundary n l m h c
      (physicalTypeILeftCoupling q hq hq1 n hn l m h c hadm hRank t).val := by
  have hp:=standardCupLeftHighest_first_boundary_signed_pos q hq hq1 l m (h+n-1) c hadm t
  rw [physicalTypeILeftCoupling_first_boundary_transport q hq hq1 n hn l m h c hadm hRank] at hp
  have hnrm:=quantumCupRankNormalization_pos q hq n hn l m h c hadm
  have he : (-1:ℝ)^(m-t.val.val)*(quantumCupRankNormalization q hq n hn l m h c hadm *
      quantumCupRankGauge n m * physicalTypeIFirstBoundary n l m h c
        (physicalTypeILeftCoupling q hq hq1 n hn l m h c hadm hRank t).val) =
      quantumCupRankNormalization q hq n hn l m h c hadm *
        (typeIFirstBoundarySign n m t.val.val * physicalTypeIFirstBoundary n l m h c
          (physicalTypeILeftCoupling q hq hq1 n hn l m h c hadm hRank t).val) := by
    unfold typeIFirstBoundarySign
    ring
  rw [he] at hp
  exact (mul_pos_iff_of_pos_left hnrm).mp hp

theorem physicalTypeIRightCoupling_unique_boundary (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m h c : ℕ) (hadm : m≤l+c) (hRank : h=0 ∨ n=1)
    (t : QuantumCupIndex l m c)
    (v : physicalQuantumHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m h c)
    (hv : v∈physicalTypeIRightChannelSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m h c t)
    (hvn : physicalTripleBilin q n l (m+h) c v.val v.val=1)
    (hvb : 0 < typeIFirstBoundarySign n m t.val.val*physicalTypeIFirstBoundary n l m h c v.val) :
    v=physicalTypeIRightCoupling q hq hq1 n hn l m h c hadm hRank t := by
  obtain ⟨e,he,hV⟩:=physicalTypeIRightCoupling_unique_sign q hq hq1 n hn l m h c hadm hRank t v hv hvn
  have hp:=physicalTypeIRightCoupling_first_boundary_signed_pos q hq hq1 n hn l m h c hadm hRank t
  rcases he with rfl|rfl
  · simpa only [one_smul] using hV
  · rw [hV] at hvb
    simp only [Submodule.coe_smul_of_tower,map_smul,smul_eq_mul] at hvb
    nlinarith

theorem physicalTypeILeftCoupling_unique_boundary (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m h c : ℕ) (hadm : m≤l+c) (hRank : h=0 ∨ n=1)
    (t : QuantumCupIndex l m c)
    (v : physicalQuantumHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m h c)
    (hv : v∈physicalTypeILeftChannelSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m h c t)
    (hvn : physicalTripleBilin q n l (m+h) c v.val v.val=1)
    (hvb : 0 < typeIFirstBoundarySign n m t.val.val*physicalTypeIFirstBoundary n l m h c v.val) :
    v=physicalTypeILeftCoupling q hq hq1 n hn l m h c hadm hRank t := by
  obtain ⟨e,he,hV⟩:=physicalTypeILeftCoupling_unique_sign q hq hq1 n hn l m h c hadm hRank t v hv hvn
  have hp:=physicalTypeILeftCoupling_first_boundary_signed_pos q hq hq1 n hn l m h c hadm hRank t
  rcases he with rfl|rfl
  · simpa only [one_smul] using hV
  · rw [hV] at hvb
    simp only [Submodule.coe_smul_of_tower,map_smul,smul_eq_mul] at hvb
    nlinarith

end AMSPhysical
#print axioms AMSPhysical.physicalTypeILeftCoupling_unique_boundary
#print axioms AMSPhysical.physicalTypeIRightCoupling_unique_boundary
