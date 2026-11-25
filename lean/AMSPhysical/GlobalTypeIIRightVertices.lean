import GlobalTypeIIRightFixedChannel
import PhysicalTypeIIHighestTreeEmbedding

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def globalMixedPairClebsch (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (p s r : ℕ) :=
  (globalMixedPairRealization q hq hq1 n hn p s r).channel.subtype.comp
    ((globalMixedPairRealization q hq hq1 n hn p s 0).transport (ne_of_gt hq)
      (globalMixedPairRealization q hq hq1 n hn p s r)).toLinearMap

theorem globalMixedPairClebsch_intertwines (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (p s r : ℕ) (z : UqTypeA q n)
    (x : (globalMixedPairRealization q hq hq1 n hn p s 0).channel) :
    globalMixedPairClebsch q hq hq1 n hn p s r
      ((globalMixedPairRealization q hq hq1 n hn p s 0).channelAction z x) =
      typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n (p+r) (s+r) z
        (globalMixedPairClebsch q hq hq1 n hn p s r x) :=
  (globalMixedPairRealization q hq hq1 n hn p s 0).transport_intertwines (ne_of_gt hq)
    (globalMixedPairRealization q hq hq1 n hn p s r) z x

theorem globalMixedPairClebsch_isometry (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (p s r : ℕ) (x y : (globalMixedPairRealization q hq hq1 n hn p s 0).channel) :
    mixedTensorBilin q n (p+r) (s+r) (globalMixedPairClebsch q hq hq1 n hn p s r x)
      (globalMixedPairClebsch q hq hq1 n hn p s r y) = mixedTensorBilin q n p s x.val y.val :=
  ((globalMixedPairRealization q hq hq1 n hn p s 0).transport_isometry (ne_of_gt hq)
    (globalMixedPairRealization q hq hq1 n hn p s r) x y).symm

def globalTypeIIRightFullTree (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a p s d : ℕ) (hbal : a+p=s+d) (hs : s≤a) (r : ℕ) :=
  physicalTypeIIUnitHighestTreeMap q hq hq1 (h+1) (by omega) a (p+r) (s+r) d
    (globalTypeIIRightVector q hq hq1 h a p s d hbal hs r)
    (physicalTypeIICalibratedRight_unit q hq hq1 h a (p+r) (s+r) d (by omega) _)

theorem globalTypeIIRightFullTree_intertwines (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a p s d : ℕ) (hbal : a+p=s+d) (hs : s≤a) (r : ℕ) (z : UqTypeA q (h+1))
    (x : quantumOccupationSpace ℝ (Fin (h+2)) d) :
    globalTypeIIRightFullTree q hq hq1 h a p s d hbal hs r
      (typeAFiniteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) d z x) =
      typeATypeIITriple q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) a (p+r) (s+r) z
        (globalTypeIIRightFullTree q hq hq1 h a p s d hbal hs r x) :=
  physicalTypeIIUnitHighestTreeMap_intertwines q hq hq1 (h+1) (by omega) a (p+r) (s+r) d _ _ z x

theorem globalTypeIIRightFullTree_highest (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a p s d : ℕ) (hbal : a+p=s+d) (hs : s≤a) (r : ℕ) :
    globalTypeIIRightFullTree q hq hq1 h a p s d hbal hs r
      (quantumOccupationBasis (K:=ℝ) d (highestOccupation (h+1) d)) =
      (globalTypeIIRightVector q hq hq1 h a p s d hbal hs r).val :=
  physicalTypeIIUnitHighestTreeMap_highest q hq hq1 (h+1) (by omega) a (p+r) (s+r) d _ _

def globalSymMixedRepresentation (q : ℝ) (hq : 0<q) (hq1 : q≠1) (h a p s : ℕ) :=
  typeATensorRepresentation q (ne_of_gt hq) (h+1)
    (typeAFiniteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) a)
    (globalMixedPairRealization q hq hq1 (h+1) (by omega) p s 0).channelAction

theorem globalSymMixedProjection_intertwines (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a p s : ℕ) (z : UqTypeA q (h+1)) (v : quantumOccupationTripleSpace (h+1) a p s) :
    TensorProduct.map (LinearMap.id : quantumOccupationSpace ℝ (Fin (h+2)) a →ₗ[ℝ] _)
      (globalMixedPairRealization q hq hq1 (h+1) (by omega) p s 0).channelProjection
      (typeATypeIITriple q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) a p s z v) =
      globalSymMixedRepresentation q hq hq1 h a p s z
        (TensorProduct.map LinearMap.id
          (globalMixedPairRealization q hq hq1 (h+1) (by omega) p s 0).channelProjection v) := by
  exact typeA_intertwiner_tensor
    (V:=quantumOccupationSpace ℝ (Fin (h+2)) a)
    (W:=quantumOccupationSpace ℝ (Fin (h+2)) p ⊗[ℝ] quantumOccupationSpace ℝ (Fin (h+2)) s)
    (V':=quantumOccupationSpace ℝ (Fin (h+2)) a)
    (W':=(globalMixedPairRealization q hq hq1 (h+1) (by omega) p s 0).channel)
    q (ne_of_gt hq) (h+1) _ _ _ _ LinearMap.id _ (fun _ _=>rfl)
    (globalMixedPairRealization q hq hq1 (h+1) (by omega) p s 0).channelProjection_intertwines z v

/-- The second Type-II right vertex is fixed at contraction zero. Its
parameters are exactly the incident triple (S_a,M_(p,s);S_d). -/
def globalSymMixedVertex (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a p s d : ℕ) (hbal : a+p=s+d) (hs : s≤a) :=
  (TensorProduct.map
    (LinearMap.id : quantumOccupationSpace ℝ (Fin (h+2)) a →ₗ[ℝ] _)
    (globalMixedPairRealization q hq hq1 (h+1) (by omega) p s 0).channelProjection).comp
      (globalTypeIIRightFullTree q hq hq1 h a p s d hbal hs 0)

theorem globalSymMixedVertex_intertwines (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a p s d : ℕ) (hbal : a+p=s+d) (hs : s≤a) (z : UqTypeA q (h+1))
    (x : quantumOccupationSpace ℝ (Fin (h+2)) d) :
    globalSymMixedVertex q hq hq1 h a p s d hbal hs
      (typeAFiniteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) d z x) =
      globalSymMixedRepresentation q hq hq1 h a p s z
        (globalSymMixedVertex q hq hq1 h a p s d hbal hs x) := by
  unfold globalSymMixedVertex
  simp only [LinearMap.comp_apply]
  rw [globalTypeIIRightFullTree_intertwines]
  exact globalSymMixedProjection_intertwines q hq hq1 h a p s z _

/-- Actual calibrated Type-II right highest trees factor through the SAME
second vertex for every realization of the intermediate mixed irrep. -/
theorem globalTypeIIRightVertex_highest_factor (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a p s d : ℕ) (hbal : a+p=s+d) (hs : s≤a) (r : ℕ) :
    TensorProduct.map (LinearMap.id : quantumOccupationSpace ℝ (Fin (h+2)) a →ₗ[ℝ] _)
      (globalMixedPairClebsch q hq hq1 (h+1) (by omega) p s r)
      (globalSymMixedVertex q hq hq1 h a p s d hbal hs
        (quantumOccupationBasis (K:=ℝ) d (highestOccupation (h+1) d))) =
      (globalTypeIIRightVector q hq hq1 h a p s d hbal hs r).val := by
  unfold globalSymMixedVertex globalTypeIIRightFullTree
  simp only [LinearMap.comp_apply,physicalTypeIIUnitHighestTreeMap_highest]
  rw [tensorRight_map_comp]
  change TensorProduct.map LinearMap.id
    (globalMixedPairTransfer q hq hq1 (h+1) (by omega) p s 0 r)
      (globalTypeIIRightVector q hq hq1 h a p s d hbal hs 0).val = _
  exact (globalTypeIIRightVector_from_zero q hq hq1 h a p s d hbal hs r).symm

theorem globalTypeIIRightComposed_intertwines (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a p s d : ℕ) (hbal : a+p=s+d) (hs : s≤a) (r : ℕ) (z : UqTypeA q (h+1))
    (x : quantumOccupationSpace ℝ (Fin (h+2)) d) :
    TensorProduct.map (LinearMap.id : quantumOccupationSpace ℝ (Fin (h+2)) a →ₗ[ℝ] _)
      (globalMixedPairClebsch q hq hq1 (h+1) (by omega) p s r)
      (globalSymMixedVertex q hq hq1 h a p s d hbal hs
        (typeAFiniteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) d z x)) =
      typeATypeIITriple q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) a (p+r) (s+r) z
        (TensorProduct.map LinearMap.id (globalMixedPairClebsch q hq hq1 (h+1) (by omega) p s r)
          (globalSymMixedVertex q hq hq1 h a p s d hbal hs x)) := by
  rw [globalSymMixedVertex_intertwines]
  exact typeA_intertwiner_tensor
    (V:=quantumOccupationSpace ℝ (Fin (h+2)) a)
    (W:=(globalMixedPairRealization q hq hq1 (h+1) (by omega) p s 0).channel)
    (V':=quantumOccupationSpace ℝ (Fin (h+2)) a)
    (W':=quantumOccupationSpace ℝ (Fin (h+2)) (p+r) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (h+2)) (s+r))
    q (ne_of_gt hq) (h+1) _ _ _ _ LinearMap.id _ (fun _ _=>rfl)
    (globalMixedPairClebsch_intertwines q hq hq1 (h+1) (by omega) p s r) z _

/-- Full actual Type-II right tree factorization, for every output-irrep
vector, through vertices depending only on their three incident labels. -/
theorem globalTypeIIRightFullTree_factor (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a p s d : ℕ) (hbal : a+p=s+d) (hs : s≤a) (r : ℕ) :
    (TensorProduct.map (LinearMap.id : quantumOccupationSpace ℝ (Fin (h+2)) a →ₗ[ℝ] _)
      (globalMixedPairClebsch q hq hq1 (h+1) (by omega) p s r)).comp
        (globalSymMixedVertex q hq hq1 h a p s d hbal hs) =
      globalTypeIIRightFullTree q hq hq1 h a p s d hbal hs r := by
  apply CompactHighestRealization.full_intertwiner_unique
    (symmetricHighestRealization q hq hq1 (h+1) d)
    (symmetricHighestRealization_channel_top q hq hq1 (h+1) d)
    (typeATypeIITriple q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) a (p+r) (s+r))
  · exact globalTypeIIRightComposed_intertwines q hq hq1 h a p s d hbal hs r
  · exact globalTypeIIRightFullTree_intertwines q hq hq1 h a p s d hbal hs r
  · change _ = globalTypeIIRightFullTree q hq hq1 h a p s d hbal hs r
      (quantumOccupationBasis (K:=ℝ) d (highestOccupation (h+1) d))
    rw [globalTypeIIRightFullTree_highest]
    exact globalTypeIIRightVertex_highest_factor q hq hq1 h a p s d hbal hs r

theorem globalMixedPairClebsch_zero (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (p s : ℕ) : globalMixedPairClebsch q hq hq1 n hn p s 0 =
      (globalMixedPairRealization q hq hq1 n hn p s 0).channel.subtype := by
  apply LinearMap.ext
  intro x
  exact congrArg Subtype.val ((globalMixedPairRealization q hq hq1 n hn p s 0).transport_self (ne_of_gt hq) x)

/-- The outer vertex is normalized in the actual product metric on the
fixed mixed carrier, written as its canonical isometric inclusion. -/
theorem globalSymMixedVertex_isometry (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a p s d : ℕ) (hbal : a+p=s+d) (hs : s≤a)
    (x y : quantumOccupationSpace ℝ (Fin (h+2)) d) :
    physicalTypeIITripleBilin q (h+1) a p s
      (TensorProduct.map LinearMap.id (globalMixedPairRealization q hq hq1 (h+1) (by omega) p s 0).channel.subtype
        (globalSymMixedVertex q hq hq1 h a p s d hbal hs x))
      (TensorProduct.map LinearMap.id (globalMixedPairRealization q hq hq1 (h+1) (by omega) p s 0).channel.subtype
        (globalSymMixedVertex q hq hq1 h a p s d hbal hs y)) =
      occupationCompactBilin q (h+1) d x y := by
  have he:=globalTypeIIRightFullTree_factor q hq hq1 h a p s d hbal hs 0
  rw [globalMixedPairClebsch_zero] at he
  have hx:=DFunLike.congr_fun he x
  have hy:=DFunLike.congr_fun he y
  simp only [LinearMap.comp_apply] at hx hy
  rw [hx,hy]
  exact physicalTypeIIUnitHighestTreeMap_isometry q hq hq1 (h+1) (by omega) a p s d _ _ x y

end AMSPhysical
#print axioms AMSPhysical.globalTypeIIRightVertex_highest_factor
#print axioms AMSPhysical.globalTypeIIRightFullTree_factor
#print axioms AMSPhysical.globalSymMixedVertex_isometry
