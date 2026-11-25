import StandardHighestFirstBoundary
import PhysicalHighestFirstBoundaryTransport

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

/-- The contraction-zero Type-I left tree is positive at the coefficient
that projects its first mixed input onto its actual normalized highest vector. -/
theorem physicalTypeILeftCoupling_zero_highest_first_pos (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m h c : ℕ) (hm : m≤c) (hRank : h=0 ∨ n=1) :
    0 < physicalHighestFirstBoundary n l m h c
      (physicalTypeILeftCoupling q hq hq1 n hn l m h c (by omega) hRank
        ⟨⟨0,by omega⟩,by constructor <;> simp_all⟩).val := by
  have he:=fullHighestRankReduction_highest_first_boundary q hq hq1 n hn l m h c hm (by omega) hRank
    (physicalTypeILeftCoupling q hq hq1 n hn l m h c (by omega) hRank
      ⟨⟨0,by omega⟩,by constructor <;> simp_all⟩)
  rw [physicalTypeILeftCoupling_rank_image,rankTwoHighestEquiv_literal,
    rankTwoMixedTripleEquiv_highest_first_boundary l m (h+n-1) c hm] at he
  have hp:=standardCupLeftHighest_zero_highest_first_pos q hq hq1 l m (h+n-1) c hm
  rw [he] at hp
  exact (mul_pos_iff_of_pos_left
    (mul_pos (quantumCupRankNormalization_pos q hq n hn l m h c (by omega)) (zpow_pos hq _))).mp hp

end AMSPhysical
#print axioms AMSPhysical.physicalTypeILeftCoupling_zero_highest_first_pos
