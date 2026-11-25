import QuantumCupHighestCoordinates

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical

/-- The independently constructed finite physical cups exhaust the ENTIRE
actual highest space, by proved Hom bending and complete pair fusion. -/
theorem physicalQuantumCupSpan_eq_highest (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m h c : ℕ) (hadm : m≤l+c) (hRank : h=0 ∨ n=1) :
    physicalQuantumCupSpan q n l m h c = typeAHighestSpace (V:=quantumOccupationTripleSpace n l (m+h) c) q n
      (typeAMixedTriple q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l (m+h) c)
      (mixedHighestDynkin n (l+c-m+h) 0) := by
  let V := quantumOccupationTripleSpace n l (m+h) c
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  letI : Module.Finite ℝ V := Module.Finite.of_basis (occupationTripleBasis n l (m+h) c)
  apply Submodule.eq_of_le_of_finrank_le
    (physicalQuantumCupSpan_le_symmetric_highest q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      n l m h c hRank)
  have hb := Module.finrank_eq_card_basis (physicalQuantumCupBasis q hq n hn l m h c)
  rw [hb]
  exact physicalTripleHighest_finrank_le q hq hq1 n hn l m h c hadm hRank

theorem physicalQuantumCupSpan_eq_full_weight (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m h c : ℕ) (hadm : m≤l+c) (hRank : h=0 ∨ n=1) :
    physicalQuantumCupSpan q n l m h c = typeAHighestSpace (V:=quantumOccupationTripleSpace n l (m+h) c) q n
      (typeAMixedTriple q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l (m+h) c)
      (mixedHighestDynkin n (l+c-m) h) := by
  rw [physicalQuantumCupSpan_eq_highest q hq hq1 n hn l m h c hadm hRank,
    mixedHighestDynkin_shifted_rank n (l+c-m) h hRank]

end AMSPhysical
#print axioms AMSPhysical.physicalQuantumCupSpan_eq_highest
