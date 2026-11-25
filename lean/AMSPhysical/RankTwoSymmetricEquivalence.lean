import TwoVertexFullIntertwiner
import TwoVertexReconstruction
import TwoVertexIsometry
import QuantumRankTwoAlgebra
import QuantumTypeAIntertwiner

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

theorem twoVertexOccupation_rankTwo_surjective (L : ℕ) :
    Function.Surjective (twoVertexOccupation 1 (by omega) L) := by
  intro y
  obtain ⟨k,hk⟩ : ∃ k,y=twoVertexOccupation 1 (by omega) L k := by
    exact ⟨_,occupation_twoVertex_reconstruction 1 (by omega) L y (by
      intro j hj0 hj1
      fin_cases j <;> contradiction)⟩
  exact ⟨k,hk.symm⟩

def rankTwoOccupationEquiv (L : ℕ) : Fin (L+1) ≃ occupationWeights (Fin 2) L :=
  Equiv.ofBijective (twoVertexOccupation 1 (by omega) L)
    ⟨twoVertexOccupation_injective 1 (by omega) L,twoVertexOccupation_rankTwo_surjective L⟩

/-- The full rank-two symmetric module is exactly the standard finite sl2
module, via the literal occupation basis rather than an assumed identification. -/
def rankTwoSymmetricEquiv (L : ℕ) :
    finiteWeightSpace (K:=ℝ) L ≃ₗ[ℝ] quantumOccupationSpace ℝ (Fin 2) L :=
  (standardWeightBasis (K:=ℝ) L).repr.trans
    ((Finsupp.domLCongr (rankTwoOccupationEquiv L)).trans
      (quantumOccupationBasis (K:=ℝ) (ι:=Fin 2) L).repr.symm)

theorem rankTwoSymmetricEquiv_eq_embedding (L : ℕ) :
    (rankTwoSymmetricEquiv L).toLinearMap=twoVertexEmbedding 1 (by omega) L := by
  apply (standardWeightBasis (K:=ℝ) L).ext
  intro k
  simp [rankTwoSymmetricEquiv,rankTwoOccupationEquiv,twoVertexEmbedding_basis]

theorem rankTwoSymmetricEquiv_isometry (q : ℝ) (hq : 0<q) (hq1 : q≠1) (L : ℕ)
    (v w : finiteWeightSpace (K:=ℝ) L) :
    occupationCompactBilin q 1 L (rankTwoSymmetricEquiv L v) (rankTwoSymmetricEquiv L w)=quantumBilin q L v w := by
  change occupationCompactBilin q 1 L ((rankTwoSymmetricEquiv L).toLinearMap v) ((rankTwoSymmetricEquiv L).toLinearMap w)=_
  rw [rankTwoSymmetricEquiv_eq_embedding]
  exact twoVertexEmbedding_isometry q hq hq1 1 (by omega) L v w

theorem rankTwoSymmetricEquiv_intertwines (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (L : ℕ) (z : UqTypeA q 1) (v : finiteWeightSpace (K:=ℝ) L) :
    rankTwoSymmetricEquiv L (finiteQuantumRepresentation q hq hD L (rankTwoToSL2 q z) v)=
      typeAFiniteQuantumRepresentation q hq hD 1 L z (rankTwoSymmetricEquiv L v) := by
  change (rankTwoSymmetricEquiv L).toLinearMap
    (((finiteQuantumRepresentation q hq hD L).comp (rankTwoToSL2 q)) z v)=
    typeAFiniteQuantumRepresentation q hq hD 1 L z ((rankTwoSymmetricEquiv L).toLinearMap v)
  rw [rankTwoSymmetricEquiv_eq_embedding]
  apply typeA_intertwiner_of_generators q 1
    ((finiteQuantumRepresentation q hq hD L).comp (rankTwoToSL2 q))
    (typeAFiniteQuantumRepresentation q hq hD 1 L) (twoVertexEmbedding 1 (by omega) L) _ z v
  intro i t w
  have hi : i=0 := Subsingleton.elim _ _
  subst i
  simp only [AlgHom.comp_apply,rankTwoToSL2_generator]
  rw [show uqGenerator q t=RingQuot.mkAlgHom ℝ (QuantumSL2Relation q) (FreeAlgebra.ι ℝ t) from rfl,
    finiteQuantumRepresentation_generator]
  fin_cases t
  · exact twoVertexEmbedding_E q hq hD 1 (by omega) L w
  · exact twoVertexEmbedding_F q hq hD 1 (by omega) L w
  · exact twoVertexEmbedding_K q hq hD 1 (by omega) L w
  · exact twoVertexEmbedding_Kinv q hq hD 1 (by omega) L w

end AMSPhysical
#print axioms AMSPhysical.rankTwoSymmetricEquiv_intertwines
