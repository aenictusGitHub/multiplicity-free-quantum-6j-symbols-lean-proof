import QuantumTypeIILeftTree
import FiniteBendingRange

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def physicalTypeIILeftChannel (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c d : ℕ) (r : TypeIICommonIndex a b c d) :
    Submodule ℝ (quantumOccupationTripleSpace n a b c) :=
  LinearMap.range ((TensorProduct.assoc ℝ _ _ _).toLinearMap.comp
    (TensorProduct.map (typeIILeftTarget q hq hq1 n hn a b c d r).channel.subtype
      (LinearMap.id : Module.End ℝ (quantumOccupationSpace ℝ (Fin (n+1)) c))))

theorem physicalTypeIILeftTreeMap_mem (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) d) :
    physicalTypeIILeftTreeMap q hq hq1 n hn a b c d hbal r v∈
      physicalTypeIILeftChannel q hq hq1 n hn a b c d r := by
  have hm : ∀ v,physicalTypeIILeftPairMap q hq hq1 n hn a b c d hbal r v∈
      (typeIILeftTarget q hq hq1 n hn a b c d r).channel := by
    intro x
    let V:=quantumOccupationSpace ℝ (Fin (n+1)) d ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) c
    let W:=quantumOccupationSpace ℝ (Fin (n+1)) a ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) b
    letI : AddCommGroup V:=inferInstance
    letI : Module ℝ V:=inferInstance
    letI : AddCommGroup W:=inferInstance
    letI : Module ℝ W:=inferInstance
    letI : Module.Finite ℝ V:=Module.Finite.of_basis
      ((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) d).tensorProduct (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) c))
    exact CompactHighestRealization.channelTransfer_mem (V:=V) (W:=W) (ne_of_gt hq)
      (typeIILeftSource q hq hq1 n hn a b c d hbal r) (typeIILeftTarget q hq hq1 n hn a b c d r) x
  obtain ⟨w,hw⟩:=bendRight_mem_tensor_range
    (typeIILeftTarget q hq hq1 n hn a b c d r).channel
    (physicalTypeIILeftPairMap q hq hq1 n hn a b c d hbal r) hm (symmetricCoevaluation q n c) v
  refine ⟨w,?_⟩
  change (TensorProduct.assoc ℝ _ _ _) (TensorProduct.map _ _ w)=_
  rw [hw,symmetricCoevaluation_diagonal]
  rfl

theorem physicalTypeIILeftHighest_mem (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d) :
    (physicalTypeIILeftHighest q hq hq1 n hn a b c d hbal r).val∈
      physicalTypeIILeftChannel q hq hq1 n hn a b c d r :=
  physicalTypeIILeftTreeMap_mem q hq hq1 n hn a b c d hbal r _

theorem physicalTypeIITripleBilin_nonneg (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c : ℕ) (v : quantumOccupationTripleSpace n a b c) :
    0≤physicalTypeIITripleBilin q n a b c v v := by
  rw [← physicalTypeIIToI_isometry q hq hq1 n hn a b c v v]
  exact physicalTripleBilin_nonneg q hq n a c b _

theorem physicalTypeIILeftHighest_norm_pos (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d) :
    0<physicalTypeIITripleBilin q n a b c
      (physicalTypeIILeftHighest q hq hq1 n hn a b c d hbal r).val
      (physicalTypeIILeftHighest q hq hq1 n hn a b c d hbal r).val := by
  apply lt_of_le_of_ne (physicalTypeIITripleBilin_nonneg q hq hq1 n hn a b c _)
  intro hz
  have he:=physicalTypeIITripleBilin_definite q hq hq1 n hn a b c _ hz.symm
  exact physicalTypeIILeftHighest_ne_zero q hq hq1 n hn a b c d hbal r (Subtype.ext he)

end AMSPhysical
#print axioms AMSPhysical.physicalTypeIILeftHighest_norm_pos
#print axioms AMSPhysical.physicalTypeIILeftHighest_mem
