import RankTwoMixedTensorEquivalence
import QuantumTripleRepresentation
import QuantumRecouplingConstruction
import QuantumTypeIITriple

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def rankTwoRightTypeIITripleEquiv (l m c : ℕ) :
    finiteWeightSpace (K:=ℝ) l ⊗[ℝ] (finiteWeightSpace (K:=ℝ) m ⊗[ℝ] finiteWeightSpace (K:=ℝ) c) ≃ₗ[ℝ]
      quantumOccupationTripleSpace 1 l m c :=
  TensorProduct.congr (rankTwoSymmetricEquiv l) (rankTwoMixedPairEquiv m c)

def rankTwoTypeIITripleEquiv (l m c : ℕ) :
    RealQuantumTripleSpace l m c ≃ₗ[ℝ] quantumOccupationTripleSpace 1 l m c :=
  (TensorProduct.assoc ℝ _ _ _).trans (rankTwoRightTypeIITripleEquiv l m c)

theorem rankTwoRightTypeIITripleEquiv_intertwines (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (l m c : ℕ) (z : UqTypeA q 1)
    (v : finiteWeightSpace (K:=ℝ) l ⊗[ℝ] (finiteWeightSpace (K:=ℝ) m ⊗[ℝ] finiteWeightSpace (K:=ℝ) c)) :
    rankTwoRightTypeIITripleEquiv l m c (finiteRightTripleRepresentation q hq hD l m c (rankTwoToSL2 q z) v)=
      typeATypeIITriple q hq hD 1 l m c z (rankTwoRightTypeIITripleEquiv l m c v) := by
  change TensorProduct.map (rankTwoSymmetricEquiv l).toLinearMap (rankTwoMixedPairEquiv m c).toLinearMap
    (((tensorRepresentation q hq (finiteQuantumRepresentation q hq hD l) (finiteTensorRepresentation q hq hD m c)).comp
      (rankTwoToSL2 q)) z v)=_
  rw [← rankTwo_tensor_pullback]
  exact typeA_intertwiner_tensor
    (V:=finiteWeightSpace (K:=ℝ) l)
    (W:=finiteWeightSpace (K:=ℝ) m ⊗[ℝ] finiteWeightSpace (K:=ℝ) c)
    (V':=quantumOccupationSpace ℝ (Fin 2) l)
    (W':=quantumOccupationSpace ℝ (Fin 2) m ⊗[ℝ] quantumOccupationSpace ℝ (Fin 2) c)
    q hq 1 _ _ _ _ _ _
    (rankTwoSymmetricEquiv_intertwines q hq hD l) (rankTwoMixedPairEquiv_intertwines q hq hD m c) z v

theorem rankTwoTypeIITripleEquiv_intertwines (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (l m c : ℕ) (z : UqTypeA q 1) (v : RealQuantumTripleSpace l m c) :
    rankTwoTypeIITripleEquiv l m c (finiteTripleRepresentation q hq hD l m c (rankTwoToSL2 q z) v)=
      typeATypeIITriple q hq hD 1 l m c z (rankTwoTypeIITripleEquiv l m c v) := by
  unfold rankTwoTypeIITripleEquiv
  simp only [LinearEquiv.trans_apply]
  have ha := finiteTripleRepresentation_assoc q hq hD l m c (rankTwoToSL2 q z) v
  change finiteRightTripleRepresentation q hq hD l m c (rankTwoToSL2 q z)
    ((TensorProduct.assoc ℝ _ _ _) v)=(TensorProduct.assoc ℝ _ _ _)
      (finiteTripleRepresentation q hq hD l m c (rankTwoToSL2 q z) v) at ha
  rw [← ha,rankTwoRightTypeIITripleEquiv_intertwines]

theorem rankTwoRightTypeIITripleEquiv_isometry (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m c : ℕ)
    (v w : finiteWeightSpace (K:=ℝ) l ⊗[ℝ] (finiteWeightSpace (K:=ℝ) m ⊗[ℝ] finiteWeightSpace (K:=ℝ) c)) :
    physicalTypeIITripleBilin q 1 l m c (rankTwoRightTypeIITripleEquiv l m c v) (rankTwoRightTypeIITripleEquiv l m c w)=
      quantumRightTripleBilin q l m c v w := by
  let V := finiteWeightSpace (K:=ℝ) l
  let W := finiteWeightSpace (K:=ℝ) m ⊗[ℝ] finiteWeightSpace (K:=ℝ) c
  let V' := quantumOccupationSpace ℝ (Fin 2) l
  let W' := quantumOccupationSpace ℝ (Fin 2) m ⊗[ℝ] quantumOccupationSpace ℝ (Fin 2) c
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  letI : AddCommGroup W := inferInstance
  letI : Module ℝ W := inferInstance
  letI : AddCommGroup V' := inferInstance
  letI : Module ℝ V' := inferInstance
  letI : AddCommGroup W' := inferInstance
  letI : Module ℝ W' := inferInstance
  exact tensorWeightedBilin_map_isometry
    (V:=V)
    (W:=W)
    (V':=V')
    (W':=W')
    (standardWeightBasis (K:=ℝ) l)
    ((standardWeightBasis (K:=ℝ) m).tensorProduct (standardWeightBasis (K:=ℝ) c))
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin 2) l)
    ((quantumOccupationBasis (K:=ℝ) (ι:=Fin 2) m).tensorProduct (quantumOccupationBasis (K:=ℝ) (ι:=Fin 2) c))
    (fun k =>quantumWeight q l k.val)
    (fun jk =>quantumWeight q m jk.1.val*quantumWeight q c jk.2.val)
    (occupationCompactWeight q 1 l)
    (fun yz =>occupationCompactWeight q 1 m yz.1*occupationOppositeWeight q 1 c yz.2)
    (rankTwoSymmetricEquiv l).toLinearMap (rankTwoMixedPairEquiv m c).toLinearMap
    (fun p u => by
      have he:=rankTwoSymmetricEquiv_isometry q hq hq1 l p u
      unfold occupationCompactBilin quantumBilin finiteWeightedBilin at he
      exact he)
    (fun p u => by
      have he:=rankTwoMixedPairEquiv_isometry q hq hq1 m c p u
      unfold mixedTensorBilin quantumTensorBilin tensorWeightedBilin finiteWeightedBilin at he
      exact he) v w

theorem rankTwoTypeIITripleEquiv_isometry (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m c : ℕ)
    (v w : RealQuantumTripleSpace l m c) :
    physicalTypeIITripleBilin q 1 l m c (rankTwoTypeIITripleEquiv l m c v) (rankTwoTypeIITripleEquiv l m c w)=
      quantumTripleBilin q l m c v w := by
  unfold rankTwoTypeIITripleEquiv
  simp only [LinearEquiv.trans_apply]
  rw [rankTwoRightTypeIITripleEquiv_isometry q hq hq1,quantumTriple_assoc_isometry]

end AMSPhysical
#print axioms AMSPhysical.rankTwoTypeIITripleEquiv_intertwines
#print axioms AMSPhysical.rankTwoTypeIITripleEquiv_isometry
