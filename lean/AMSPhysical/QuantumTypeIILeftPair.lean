import CompactHighestChannelTransfer
import QuantumTwoRowCanonicalClebsch
import QuantumPhysicalTripleInstances

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

abbrev TypeIICommonIndex (a b c d : ℕ) := Fin (min (min a b) (min c d)+1)

def typeIILeftSource (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d) :=
  twoRowHighestRealization q hq hq1 n hn (a+b) r.val d c (by omega) (by have h:=r.isLt;omega) (by have h:=r.isLt;omega)

def typeIILeftTarget (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c d : ℕ) (r : TypeIICommonIndex a b c d) :=
  twoRowHighestRealization q hq hq1 n hn (a+b) r.val a b rfl (by have h:=r.isLt;omega) (by have h:=r.isLt;omega)

/-- Actual full-algebra pair map selecting a common two-row irrep. -/
def physicalTypeIILeftPairMap (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d) :
    (quantumOccupationSpace ℝ (Fin (n+1)) d ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) c) →ₗ[ℝ]
    (quantumOccupationSpace ℝ (Fin (n+1)) a ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) b) := by
  let V:=quantumOccupationSpace ℝ (Fin (n+1)) d ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) c
  let W:=quantumOccupationSpace ℝ (Fin (n+1)) a ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) b
  letI : AddCommGroup V:=inferInstance
  letI : Module ℝ V:=inferInstance
  letI : AddCommGroup W:=inferInstance
  letI : Module ℝ W:=inferInstance
  letI : Module.Finite ℝ V:=Module.Finite.of_basis
    ((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) d).tensorProduct (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) c))
  exact CompactHighestRealization.channelTransfer (V:=V) (W:=W) (ne_of_gt hq)
    (typeIILeftSource q hq hq1 n hn a b c d hbal r) (typeIILeftTarget q hq hq1 n hn a b c d r)

theorem physicalTypeIILeftPairMap_intertwines (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d)
    (z : UqTypeA q n)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) d ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) c) :
    physicalTypeIILeftPairMap q hq hq1 n hn a b c d hbal r
      (typeASymmetricTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n d c z v)=
    typeASymmetricTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b z
      (physicalTypeIILeftPairMap q hq hq1 n hn a b c d hbal r v) := by
  let V:=quantumOccupationSpace ℝ (Fin (n+1)) d ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) c
  let W:=quantumOccupationSpace ℝ (Fin (n+1)) a ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) b
  letI : AddCommGroup V:=inferInstance
  letI : Module ℝ V:=inferInstance
  letI : AddCommGroup W:=inferInstance
  letI : Module ℝ W:=inferInstance
  letI : Module.Finite ℝ V:=Module.Finite.of_basis
    ((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) d).tensorProduct (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) c))
  exact CompactHighestRealization.channelTransfer_intertwines (V:=V) (W:=W) (ne_of_gt hq)
    (typeIILeftSource q hq hq1 n hn a b c d hbal r) (typeIILeftTarget q hq hq1 n hn a b c d r) z v

theorem physicalTypeIILeftPairMap_ne_zero (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d) :
    physicalTypeIILeftPairMap q hq hq1 n hn a b c d hbal r≠0 := by
  let V:=quantumOccupationSpace ℝ (Fin (n+1)) d ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) c
  let W:=quantumOccupationSpace ℝ (Fin (n+1)) a ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) b
  letI : AddCommGroup V:=inferInstance
  letI : Module ℝ V:=inferInstance
  letI : AddCommGroup W:=inferInstance
  letI : Module ℝ W:=inferInstance
  letI : Module.Finite ℝ V:=Module.Finite.of_basis
    ((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) d).tensorProduct (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) c))
  exact CompactHighestRealization.channelTransfer_ne_zero (V:=V) (W:=W) (ne_of_gt hq)
    (typeIILeftSource q hq hq1 n hn a b c d hbal r) (typeIILeftTarget q hq hq1 n hn a b c d r)

end AMSPhysical
#print axioms AMSPhysical.physicalTypeIILeftPairMap_intertwines
