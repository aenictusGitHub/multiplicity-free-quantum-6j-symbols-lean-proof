import QuantumTypeIILeftChannel
import QuantumTwoRowChannelEquality
import TensorSubmoduleOrthogonal

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem physicalTypeIITripleBilin_assoc (q : ℝ) (n a b c : ℕ)
    (v w : (quantumOccupationSpace ℝ (Fin (n+1)) a ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) b) ⊗[ℝ]
      quantumOccupationSpace ℝ (Fin (n+1)) c) :
    physicalTypeIITripleBilin q n a b c ((TensorProduct.assoc ℝ _ _ _) v) ((TensorProduct.assoc ℝ _ _ _) w)=
    tensorWeightedBilin
      ((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) a).tensorProduct (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) b))
      (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) c)
      (fun xy =>occupationCompactWeight q n a xy.1*occupationCompactWeight q n b xy.2)
      (occupationOppositeWeight q n c) v w := by
  exact tensorWeightedBilin_assoc_isometry
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) a)
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) b)
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) c)
    (occupationCompactWeight q n a) (occupationCompactWeight q n b) (occupationOppositeWeight q n c) v w

theorem physicalTypeIILeftChannels_orthogonal (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c d : ℕ) (r s : TypeIICommonIndex a b c d) (hrs : r≠s)
    (v w : quantumOccupationTripleSpace n a b c)
    (hv : v∈physicalTypeIILeftChannel q hq hq1 n hn a b c d r)
    (hw : w∈physicalTypeIILeftChannel q hq hq1 n hn a b c d s) :
    physicalTypeIITripleBilin q n a b c v w=0 := by
  obtain ⟨x,rfl⟩:=hv
  obtain ⟨y,rfl⟩:=hw
  change physicalTypeIITripleBilin q n a b c
    ((TensorProduct.assoc ℝ _ _ _) (TensorProduct.map _ _ x))
    ((TensorProduct.assoc ℝ _ _ _) (TensorProduct.map _ _ y))=0
  rw [physicalTypeIITripleBilin_assoc]
  apply tensorWeightedBilin_submodule_orthogonal
  intro u hu z hz
  let r' : TwoRowFusionIndex a b:=⟨r.val,by have h:=r.isLt;omega⟩
  let s' : TwoRowFusionIndex a b:=⟨s.val,by have h:=s.isLt;omega⟩
  have hne : r'≠s' := by intro he;apply hrs;exact Fin.ext (congrArg (fun x : TwoRowFusionIndex a b =>x.val) he)
  exact normalizedTwoRowChannels_orthogonal q hq hq1 n hn a b r' s' hne u hu z hz

theorem physicalTypeIILeftHighest_orthogonal (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c d : ℕ) (hbal : a+b=c+d) (r s : TypeIICommonIndex a b c d) (hrs : r≠s) :
    physicalTypeIITripleBilin q n a b c
      (physicalTypeIILeftHighest q hq hq1 n hn a b c d hbal r).val
      (physicalTypeIILeftHighest q hq hq1 n hn a b c d hbal s).val=0 :=
  physicalTypeIILeftChannels_orthogonal q hq hq1 n hn a b c d r s hrs _ _
    (physicalTypeIILeftHighest_mem q hq hq1 n hn a b c d hbal r)
    (physicalTypeIILeftHighest_mem q hq hq1 n hn a b c d hbal s)

end AMSPhysical
#print axioms AMSPhysical.physicalTypeIILeftHighest_orthogonal
