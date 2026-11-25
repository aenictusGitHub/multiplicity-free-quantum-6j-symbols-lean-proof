import QuantumTripleHomEquiv
import QuantumCupHomIndex
import QuantumCupHighestWeight
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

def physicalTripleHighestCoordinates (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m h c : ℕ) :
    typeAHighestSpace (V:=quantumOccupationTripleSpace n l (m+h) c) q n
      (typeAMixedTriple q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l (m+h) c)
      (mixedHighestDynkin n (l+c-m+h) 0) →ₗ[ℝ]
      (MixedHomMatchIndex n hn (l+c-m+h) c l (m+h) → ℝ) := by
  let V := quantumOccupationTripleSpace n l (m+h) c
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  let e := (symmetricTripleHighestHomEquiv q hq hq1 n (l+c-m+h) l (m+h) c).symm.trans
    (mixedPairTripleHomEquiv q hq hq1 n (l+c-m+h) c l (m+h)).symm
  exact (mixedHomCoordinates q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn
    (l+c-m+h) c l (m+h)).comp e.toLinearMap

theorem physicalTripleHighestCoordinates_injective (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m h c : ℕ) :
    Function.Injective (physicalTripleHighestCoordinates q hq hq1 n hn l m h c) := by
  let V := quantumOccupationTripleSpace n l (m+h) c
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  exact (mixedHomCoordinates_injective q hq hq1 n hn (l+c-m+h) c l (m+h)).comp
    (((symmetricTripleHighestHomEquiv q hq hq1 n (l+c-m+h) l (m+h) c).symm.trans
      (mixedPairTripleHomEquiv q hq hq1 n (l+c-m+h) c l (m+h)).symm).injective)

theorem physicalTripleHighest_finrank_le (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m h c : ℕ) (hadm : m≤l+c) (hRank : h=0 ∨ n=1) :
    Module.finrank ℝ (typeAHighestSpace (V:=quantumOccupationTripleSpace n l (m+h) c) q n
      (typeAMixedTriple q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l (m+h) c)
      (mixedHighestDynkin n (l+c-m+h) 0)) ≤ Fintype.card (QuantumCupIndex l m c) := by
  have hh:=LinearMap.finrank_le_finrank_of_injective
    (physicalTripleHighestCoordinates_injective q hq hq1 n hn l m h c)
  rw [Module.finrank_pi] at hh
  simpa only [Module.finrank_self,Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one,
    Fintype.card_congr (mixedHomCupIndexEquiv n hn l m h c hadm hRank)] using hh

end AMSPhysical
#print axioms AMSPhysical.physicalTripleHighest_finrank_le
