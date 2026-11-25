import QuantumMixedCommutor
import QuantumPhysicalTripleInstances
import QuantumTypeATripleCompact
import TensorWeightedIsometries
import TypeAHighestSpaceEquivalence

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def typeATypeIITriple (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n a b c : ℕ) :
    UqTypeA q n →ₐ[ℝ] Module.End ℝ (quantumOccupationTripleSpace n a b c) :=
  typeATensorRepresentation q hq n (typeAFiniteQuantumRepresentation q hq hD n a)
    (typeAMixedTensor q hq hD n b c)

/-- Literal product metric on Sym_a tensor Sym_b tensor Opp_c. -/
def physicalTypeIITripleBilin (q : ℝ) (n a b c : ℕ) :
    LinearMap.BilinForm ℝ (quantumOccupationTripleSpace n a b c) :=
  tensorWeightedBilin (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) a)
    ((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) b).tensorProduct
      (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) c))
    (occupationCompactWeight q n a)
    (fun yz =>occupationCompactWeight q n b yz.1*occupationOppositeWeight q n c yz.2)

/-- Reorders the actual last mixed pair by the independently constructed
isometric module commutor. This definition makes no claim about Type-II
left-channel compatibility with rank reduction. -/
def physicalTypeIIToI (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n) (a b c : ℕ) :
    quantumOccupationTripleSpace n a b c ≃ₗ[ℝ] quantumOccupationTripleSpace n a c b :=
  TensorProduct.congr (LinearEquiv.refl ℝ (quantumOccupationSpace ℝ (Fin (n+1)) a))
    (physicalMixedCommutor q hq hq1 n hn b c)

theorem physicalTypeIIToI_intertwines (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c : ℕ) (z : UqTypeA q n) (v : quantumOccupationTripleSpace n a b c) :
    physicalTypeIIToI q hq hq1 n hn a b c
      (typeATypeIITriple q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c z v)=
    typeAMixedTriple q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a c b z
      (physicalTypeIIToI q hq hq1 n hn a b c v) := by
  exact typeA_intertwiner_tensor
    (V:=quantumOccupationSpace ℝ (Fin (n+1)) a)
    (W:=quantumOccupationSpace ℝ (Fin (n+1)) b ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) c)
    (V':=quantumOccupationSpace ℝ (Fin (n+1)) a)
    (W':=quantumOccupationSpace ℝ (Fin (n+1)) c ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) b)
    q (ne_of_gt hq) n _ _ _ _ LinearMap.id (physicalMixedCommutor q hq hq1 n hn b c).toLinearMap
    (fun _ _ =>rfl) (physicalMixedCommutor_intertwines q hq hq1 n hn b c) z v

theorem physicalTypeIIToI_isometry (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c : ℕ) (v w : quantumOccupationTripleSpace n a b c) :
    physicalTripleBilin q n a c b (physicalTypeIIToI q hq hq1 n hn a b c v)
      (physicalTypeIIToI q hq hq1 n hn a b c w)=physicalTypeIITripleBilin q n a b c v w := by
  rw [physicalTripleBilin_tensor]
  exact tensorWeightedBilin_map_isometry
    (V:=quantumOccupationSpace ℝ (Fin (n+1)) a)
    (W:=quantumOccupationSpace ℝ (Fin (n+1)) b ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) c)
    (V':=quantumOccupationSpace ℝ (Fin (n+1)) a)
    (W':=quantumOccupationSpace ℝ (Fin (n+1)) c ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) b)
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) a)
    ((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) b).tensorProduct (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) c))
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) a)
    ((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) c).tensorProduct (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) b))
    (occupationCompactWeight q n a) (fun yz =>occupationCompactWeight q n b yz.1*occupationOppositeWeight q n c yz.2)
    (occupationCompactWeight q n a) (fun yz =>occupationOppositeWeight q n c yz.1*occupationCompactWeight q n b yz.2)
    LinearMap.id (physicalMixedCommutor q hq hq1 n hn b c).toLinearMap
    (fun _ _ =>rfl)
    (fun p u =>by
      have he:=physicalMixedCommutor_isometry q hq hq1 n hn b c p u
      unfold reverseMixedTensorBilin mixedTensorBilin tensorWeightedBilin finiteWeightedBilin at he
      exact he) v w

theorem physicalTypeIITripleBilin_definite (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c : ℕ) (v : quantumOccupationTripleSpace n a b c)
    (hv : physicalTypeIITripleBilin q n a b c v v=0) : v=0 := by
  apply (physicalTypeIIToI q hq hq1 n hn a b c).injective
  rw [map_zero]
  apply physicalTripleBilin_definite q hq n a c b
  rwa [physicalTypeIIToI_isometry]

def physicalTypeIIHighestSpace (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n a b c d : ℕ) :=
  typeAHighestSpace q n (typeATypeIITriple q hq hD n a b c) (mixedHighestDynkin n d 0)

def physicalTypeIIHighestToI (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n) (a b c d : ℕ) :
    physicalTypeIIHighestSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c d ≃ₗ[ℝ]
    typeAHighestSpace q n (typeAMixedTriple q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a c b)
      (mixedHighestDynkin n d 0) :=
  typeAHighestSpaceEquiv q n _ _ (physicalTypeIIToI q hq hq1 n hn a b c)
    (physicalTypeIIToI_intertwines q hq hq1 n hn a b c) _

end AMSPhysical
#print axioms AMSPhysical.physicalTypeIIToI_isometry
#print axioms AMSPhysical.physicalTypeIIHighestToI
