import ActualSymMixedVertexEntry
import TwoRowOuterBoundaryPositive
import TypeIIChannelHighestLine

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

/-- An actual two-row carrier in any native symmetric pair. Canonicalizing
it identifies all pairs with the same actual highest weight. -/
def nativeTypeIITwoRowCarrier (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c d : ℕ) (r : TypeIICommonIndex a b c d) :=
  ActualHighestCarrier.ofChannel (typeIILeftTarget q hq hq1 n hn a b c d r)

def nativeTypeIITwoRowOut (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d) :=
  ((typeIILeftSource q hq hq1 n hn a b c d hbal r).transport (ne_of_gt hq)
    (typeIILeftTarget q hq hq1 n hn a b c d r)).toLinearMap.comp
      (typeIILeftSource q hq hq1 n hn a b c d hbal r).channelProjection

def nativeTypeIIOuterVertex (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d) :=
  globalTypeIILeftVertexScale q hq hq1 n hn (c+d) r.val d •
    bendRight (nativeTypeIITwoRowOut q hq hq1 n hn a b c d hbal r) (symmetricCoevaluation q n c)

def nativeTypeIITwoRowInclusion (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c d : ℕ) (r : TypeIICommonIndex a b c d) :=
  (TensorProduct.assoc ℝ
    (quantumOccupationSpace ℝ (Fin (n+1)) a)
    (quantumOccupationSpace ℝ (Fin (n+1)) b)
    (quantumOccupationSpace ℝ (Fin (n+1)) c)).toLinearMap.comp
      (TensorProduct.map (typeIILeftTarget q hq hq1 n hn a b c d r).channel.subtype
        (LinearMap.id : quantumOccupationSpace ℝ (Fin (n+1)) c →ₗ[ℝ] _))

theorem nativeTypeIITwoRowOut_pair_factor (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d) :
    (typeIILeftTarget q hq hq1 n hn a b c d r).channel.subtype.comp
      (nativeTypeIITwoRowOut q hq hq1 n hn a b c d hbal r) =
      physicalTypeIILeftPairMap q hq hq1 n hn a b c d hbal r := by
  rfl

theorem nativeTypeIITwoRowOut_intertwines (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d) (z : UqTypeA q n)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) d ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) c) :
    nativeTypeIITwoRowOut q hq hq1 n hn a b c d hbal r
      (typeASymmetricTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n d c z v)=
      (typeIILeftTarget q hq hq1 n hn a b c d r).channelAction z
        (nativeTypeIITwoRowOut q hq hq1 n hn a b c d hbal r v) := by
  unfold nativeTypeIITwoRowOut
  simp only [LinearMap.comp_apply,LinearEquiv.coe_coe]
  change (typeIILeftSource q hq hq1 n hn a b c d hbal r).transport (ne_of_gt hq)
    (typeIILeftTarget q hq hq1 n hn a b c d r)
    ((typeIILeftSource q hq hq1 n hn a b c d hbal r).channelProjection
      ((typeIILeftSource q hq hq1 n hn a b c d hbal r).action z v)) = _
  rw [(typeIILeftSource q hq hq1 n hn a b c d hbal r).channelProjection_intertwines]
  apply Subtype.ext
  exact (typeIILeftSource q hq hq1 n hn a b c d hbal r).transport_intertwines (ne_of_gt hq)
    (typeIILeftTarget q hq hq1 n hn a b c d r) z _

theorem nativeTypeIIOuterVertex_intertwines (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d) (z : UqTypeA q n)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) d) :
    nativeTypeIIOuterVertex q hq hq1 n hn a b c d hbal r
      (typeAFiniteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n d z v)=
      typeATensorRepresentation q (ne_of_gt hq) n
        (typeIILeftTarget q hq hq1 n hn a b c d r).channelAction
        (typeAOppositeSymmetricRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n c) z
        (nativeTypeIIOuterVertex q hq hq1 n hn a b c d hbal r v) := by
  unfold nativeTypeIIOuterVertex
  simp only [LinearMap.smul_apply]
  rw [typeA_bendRight_intertwines q (ne_of_gt hq) n
    (typeAFiniteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n d)
    (typeIILeftTarget q hq hq1 n hn a b c d r).channelAction
    (typeAFiniteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n c)
    (typeAOppositeSymmetricRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n c)
    _ _ (nativeTypeIITwoRowOut_intertwines q hq hq1 n hn a b c d hbal r)
    (symmetricCoevaluation_invariant q hq hq1 n c),map_smul]

theorem nativeTypeIITwoRowOut_tree_factor (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d) :
    (nativeTypeIITwoRowInclusion q hq hq1 n hn a b c d r).comp
      (bendRight (nativeTypeIITwoRowOut q hq hq1 n hn a b c d hbal r) (symmetricCoevaluation q n c)) =
      physicalTypeIILeftTreeMap q hq hq1 n hn a b c d hbal r := by
  unfold nativeTypeIITwoRowInclusion
  rw [LinearMap.comp_assoc,← bendRight_postcompose,nativeTypeIITwoRowOut_pair_factor]
  exact (physicalTypeIILeftTreeMap_eq_bend q hq hq1 n hn a b c d hbal r).symm

theorem nativeTypeIITwoRowOut_highest_functional (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) d ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) c) :
    (nativeTypeIITwoRowCarrier q hq hq1 n hn a b c d r).frame.pairing
      (nativeTypeIITwoRowCarrier q hq hq1 n hn a b c d r).frame.highest
      (nativeTypeIITwoRowOut q hq hq1 n hn a b c d hbal r v)=
      symmetricTensorBilin q n d c (normalizedTwoRowHighest q n hn d c r.val
        (by have hr:=r.isLt;omega) (by have hr:=r.isLt;omega)) v := by
  let X:=typeIILeftSource q hq hq1 n hn a b c d hbal r
  let Y:=typeIILeftTarget q hq hq1 n hn a b c d r
  have he:=X.transport_highest_functional (ne_of_gt hq) Y (X.channelProjection v)
  have hp:=X.channelProjection_adjoint ⟨X.highest,algebraCyclicSpan_self _ _⟩ v
  exact he.trans hp.symm

end AMSPhysical
#print axioms AMSPhysical.nativeTypeIIOuterVertex_intertwines
#print axioms AMSPhysical.nativeTypeIITwoRowOut_tree_factor
