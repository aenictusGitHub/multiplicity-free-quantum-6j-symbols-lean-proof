import RankTwoSymmetricEquivalence
import QuantumOppositeReflection
import QuantumReflectionMetric

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

theorem typeADynkinReflection_rankTwo (q : ℝ) :
    typeADynkinReflection q 1=AlgHom.id ℝ (UqTypeA q 1) := by
  apply RingQuot.ringQuot_ext'
  apply FreeAlgebra.hom_ext
  funext it
  change typeADynkinReflection q 1 (typeAAlgebraGenerator q 1 it.1 it.2)=typeAAlgebraGenerator q 1 it.1 it.2
  rw [typeADynkinReflection_generator]
  congr 1
  exact Subsingleton.elim _ _

def rankTwoOppositeEquiv (L : ℕ) :
    finiteWeightSpace (K:=ℝ) L ≃ₗ[ℝ] quantumOccupationSpace ℝ (Fin 2) L :=
  (rankTwoSymmetricEquiv L).trans (quantumOccupationReflection 1 L)

theorem rankTwoOppositeEquiv_intertwines (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (L : ℕ) (z : UqTypeA q 1) (v : finiteWeightSpace (K:=ℝ) L) :
    rankTwoOppositeEquiv L (finiteQuantumRepresentation q hq hD L (rankTwoToSL2 q z) v)=
      typeAOppositeSymmetricRepresentation q hq hD 1 L z (rankTwoOppositeEquiv L v) := by
  unfold rankTwoOppositeEquiv
  simp only [LinearEquiv.trans_apply]
  rw [rankTwoSymmetricEquiv_intertwines,quantumOccupationReflection_intertwines,
    typeADynkinReflection_rankTwo,AlgHom.id_apply]

theorem rankTwoOppositeEquiv_isometry (q : ℝ) (hq : 0<q) (hq1 : q≠1) (L : ℕ)
    (v w : finiteWeightSpace (K:=ℝ) L) :
    occupationOppositeBilin q 1 L (rankTwoOppositeEquiv L v) (rankTwoOppositeEquiv L w)=quantumBilin q L v w := by
  unfold rankTwoOppositeEquiv
  simp only [LinearEquiv.trans_apply]
  rw [quantumOccupationReflection_compact_isometry q (ne_of_gt hq),rankTwoSymmetricEquiv_isometry q hq hq1]

end AMSPhysical
#print axioms AMSPhysical.rankTwoOppositeEquiv_intertwines
