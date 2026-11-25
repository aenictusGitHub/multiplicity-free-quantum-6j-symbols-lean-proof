import QuantumTypeIIHighestBoundary
import QuantumTypeIILeftUnit
import FiniteBendingMetric

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 900000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

/-- Exact ACTUAL Type-II raw tree norm, with the opposite-leg metric
factor proved explicitly and no Wigner/AMS candidate in its definition. -/
theorem physicalTypeIILeftHighestNormSq_pair_sum (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (a b c d : ℕ) (hbal:a+b=c+d) (r:TypeIICommonIndex a b c d) :
    physicalTypeIILeftHighestNormSq q hq hq1 n hn a b c d hbal r=
      ∑ x:occupationWeights (Fin (n+1)) c,
        occupationOppositeWeight q n c x/(occupationCompactWeight q n c x*occupationCompactWeight q n c x)*
          symmetricTensorBilin q n a b
            (physicalTypeIILeftPairMap q hq hq1 n hn a b c d hbal r
              (quantumOccupationBasis (K:=ℝ) d (highestOccupation n d) ⊗ₜ[ℝ] quantumOccupationBasis (K:=ℝ) c x))
            (physicalTypeIILeftPairMap q hq hq1 n hn a b c d hbal r
              (quantumOccupationBasis (K:=ℝ) d (highestOccupation n d) ⊗ₜ[ℝ] quantumOccupationBasis (K:=ℝ) c x)) := by
  unfold physicalTypeIILeftHighestNormSq
  change physicalTypeIITripleBilin q n a b c
    (physicalTypeIILeftTreeMap q hq hq1 n hn a b c d hbal r (quantumOccupationBasis (K:=ℝ) d (highestOccupation n d)))
    (physicalTypeIILeftTreeMap q hq hq1 n hn a b c d hbal r (quantumOccupationBasis (K:=ℝ) d (highestOccupation n d)))=_
  rw [physicalTypeIILeftTreeMap_eq_bend]
  simp only [LinearMap.comp_apply,LinearEquiv.coe_coe]
  rw [physicalTypeIITripleBilin_assoc,symmetricCoevaluation_diagonal,bendRight_diagonal_metric]
  apply Finset.sum_congr rfl
  intro x hx
  change (occupationDualSign n c x/occupationCompactWeight q n c x)*
    (occupationDualSign n c x/occupationCompactWeight q n c x)*occupationOppositeWeight q n c x*
      symmetricTensorBilin q n a b _ _=_
  rw [div_mul_div_comm,occupationDualSign_square]
  ring

end AMSPhysical
#print axioms AMSPhysical.physicalTypeIILeftHighestNormSq_pair_sum
