import GlobalTypeILeftFixedChannel
import PhysicalTypeIHighestTreeEmbedding
import GlobalTypeIIRightVertices

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1200000
set_option Elab.async false
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

/-- Only the contraction-zero tree is used to define the outer vertex.
Its output degree is intrinsic to the two input irreps. -/
def globalTypeILeftFullTree (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h p s c : ℕ) (hs : s≤c) :
    quantumOccupationSpace ℝ (Fin (h+2)) (p+c-s) →ₗ[ℝ]
      quantumOccupationTripleSpace (h+1) p s c :=
  physicalTypeIUnitHighestTreeMap q hq hq1 (h+1) p s c (p+c-s)
    (globalTypeILeftVector q hq hq1 h p s c 0 hs)
    (physicalTypeILeftCoupling_unit q hq hq1 (h+1) (by omega) p s 0 c
      (by omega) (Or.inl rfl) (globalTypeILeftCupIndex p s c 0 hs))

theorem globalTypeILeftFullTree_highest (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h p s c : ℕ) (hs : s≤c) :
    globalTypeILeftFullTree q hq hq1 h p s c hs
      (quantumOccupationBasis (K:=ℝ) (p+c-s) (highestOccupation (h+1) (p+c-s))) =
      (globalTypeILeftVector q hq hq1 h p s c 0 hs).val := by
  unfold globalTypeILeftFullTree
  rw [physicalTypeIUnitHighestTreeMap_highest]

theorem globalTypeILeftFullTree_intertwines (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h p s c : ℕ) (hs : s≤c) (z : UqTypeA q (h+1))
    (x : quantumOccupationSpace ℝ (Fin (h+2)) (p+c-s)) :
    globalTypeILeftFullTree q hq hq1 h p s c hs
      (typeAFiniteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
        (h+1) (p+c-s) z x) =
      typeAMixedTriple q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) p s c z
        (globalTypeILeftFullTree q hq hq1 h p s c hs x) := by
  unfold globalTypeILeftFullTree
  exact physicalTypeIUnitHighestTreeMap_intertwines q hq hq1 (h+1) p s c (p+c-s)
    (globalTypeILeftVector q hq hq1 h p s c 0 hs)
    (physicalTypeILeftCoupling_unit q hq hq1 (h+1) (by omega) p s 0 c
      (by omega) (Or.inl rfl) (globalTypeILeftCupIndex p s c 0 hs)) z x

def globalMixedSymRepresentation (q : ℝ) (hq : 0<q) (hq1 : q≠1) (h p s c : ℕ) :=
  typeATensorRepresentation q (ne_of_gt hq) (h+1)
    (globalMixedPairRealization q hq hq1 (h+1) (by omega) p s 0).channelAction
    (typeAFiniteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) c)

def globalMixedSymProjection (q : ℝ) (hq : 0<q) (hq1 : q≠1) (h p s c : ℕ) :=
  (TensorProduct.map
    (globalMixedPairRealization q hq hq1 (h+1) (by omega) p s 0).channelProjection
    (LinearMap.id : quantumOccupationSpace ℝ (Fin (h+2)) c →ₗ[ℝ] _)).comp
      (TensorProduct.assoc ℝ
        (quantumOccupationSpace ℝ (Fin ((h+1)+1)) p)
        (quantumOccupationSpace ℝ (Fin ((h+1)+1)) s)
        (quantumOccupationSpace ℝ (Fin ((h+1)+1)) c)).symm.toLinearMap

theorem globalMixedSymProjection_intertwines (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h p s c : ℕ) (z : UqTypeA q (h+1)) (v : quantumOccupationTripleSpace (h+1) p s c) :
    globalMixedSymProjection q hq hq1 h p s c
      (typeAMixedTriple q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) p s c z v) =
      globalMixedSymRepresentation q hq hq1 h p s c z (globalMixedSymProjection q hq hq1 h p s c v) := by
  unfold globalMixedSymProjection
  simp only [LinearMap.comp_apply,LinearEquiv.coe_coe]
  have hA:=typeA_associator_inverse_intertwines q (ne_of_gt hq) (h+1)
    (typeAFiniteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) p)
    (typeAOppositeSymmetricRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) s)
    (typeAFiniteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) c) z v
  change (TensorProduct.assoc ℝ _ _ _).symm
    (typeAMixedTriple q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) p s c z v) =
      typeATensorRepresentation q (ne_of_gt hq) (h+1)
        (typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) p s)
        (typeAFiniteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) c)
        z ((TensorProduct.assoc ℝ _ _ _).symm v) at hA
  refine (congrArg (fun w => TensorProduct.map
    (globalMixedPairRealization q hq hq1 (h+1) (by omega) p s 0).channelProjection
    (LinearMap.id : quantumOccupationSpace ℝ (Fin ((h+1)+1)) c →ₗ[ℝ] _) w) hA).trans ?_
  exact typeA_intertwiner_tensor q (ne_of_gt hq) (h+1)
    (typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) p s)
    (typeAFiniteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) c)
    (globalMixedPairRealization q hq hq1 (h+1) (by omega) p s 0).channelAction
    (typeAFiniteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) c)
    _ LinearMap.id
    (globalMixedPairRealization q hq hq1 (h+1) (by omega) p s 0).channelProjection_intertwines
    (fun _ _=>rfl) z _

/-- One actual outer vertex (M_(p,s),S_c;S_d), chosen only from its
three incident representations and independent of the mixed realization. -/
def globalMixedSymVertex (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h p s c : ℕ) (hs : s≤c) :=
  (globalMixedSymProjection q hq hq1 h p s c).comp
    (globalTypeILeftFullTree q hq hq1 h p s c hs)

theorem globalMixedSymVertex_intertwines (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h p s c : ℕ) (hs : s≤c)
    (z : UqTypeA q (h+1)) (x : quantumOccupationSpace ℝ (Fin (h+2)) (p+c-s)) :
    globalMixedSymVertex q hq hq1 h p s c hs
      (typeAFiniteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) (p+c-s) z x) =
      globalMixedSymRepresentation q hq hq1 h p s c z (globalMixedSymVertex q hq hq1 h p s c hs x) := by
  unfold globalMixedSymVertex
  simp only [LinearMap.comp_apply]
  rw [globalTypeILeftFullTree_intertwines q hq hq1 h p s c hs z x]
  exact globalMixedSymProjection_intertwines q hq hq1 h p s c z _

def globalAMSMixedIn (q : ℝ) (hq : 0<q) (hq1 : q≠1) (h p s r : ℕ) :=
  (-1:ℝ)^(h*r) • globalMixedPairClebsch q hq hq1 (h+1) (by omega) p s r

theorem globalMixedSymVertex_highest_factor (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h p s c : ℕ) (hs : s≤c) (r : ℕ) :
    TensorProduct.map (globalAMSMixedIn q hq hq1 h p s r)
      (LinearMap.id : quantumOccupationSpace ℝ (Fin (h+2)) c →ₗ[ℝ] _)
      (globalMixedSymVertex q hq hq1 h p s c hs
        (quantumOccupationBasis (K:=ℝ) (p+c-s) (highestOccupation (h+1) (p+c-s)))) =
      globalTypeILeftUnassoc q hq hq1 h p s c r hs := by
  unfold globalMixedSymVertex globalMixedSymProjection globalAMSMixedIn
  simp only [LinearMap.comp_apply,LinearEquiv.coe_coe]
  rw [globalTypeILeftFullTree_highest q hq hq1 h p s c hs]
  rw [TensorProduct.map_smul_left,LinearMap.smul_apply,tensorLeft_map_comp]
  change (-1:ℝ)^(h*r) • TensorProduct.map
    (globalMixedPairTransfer q hq hq1 (h+1) (by omega) p s 0 r) LinearMap.id
    (globalTypeILeftUnassoc q hq hq1 h p s c 0 hs) = _
  exact (globalTypeILeftUnassoc_from_zero q hq hq1 h p s c r hs).symm

end AMSPhysical
#print axioms AMSPhysical.globalMixedSymVertex_highest_factor
#print axioms AMSPhysical.globalMixedSymVertex_intertwines
