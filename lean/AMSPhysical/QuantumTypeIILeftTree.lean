import QuantumTypeIILeftPair
import QuantumOppositeHomBending
import QuantumTypeIITriple
import QuantumSymmetricHighestRealization
import CompactHighestHomEquivalence
import QuantumTypeAIrreducible

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def physicalTypeIILeftPairHom (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d) :
    algebraIntertwinerSpace (typeASymmetricTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n d c)
      (typeASymmetricTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b) :=
  ⟨physicalTypeIILeftPairMap q hq hq1 n hn a b c d hbal r,
    physicalTypeIILeftPairMap_intertwines q hq hq1 n hn a b c d hbal r⟩

def physicalTypeIILeftBentHom (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d) :=
  oppositeRightHomBending q hq hq1 n c
    (typeAFiniteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n d)
    (typeASymmetricTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b)
    (physicalTypeIILeftPairHom q hq hq1 n hn a b c d hbal r)

/-- The actual Type-II left tree, obtained by physically bending the common
two-row pair intertwiner; no candidate factorial formula defines this map. -/
def physicalTypeIILeftTreeMap (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d) :
    quantumOccupationSpace ℝ (Fin (n+1)) d →ₗ[ℝ] quantumOccupationTripleSpace n a b c :=
  (TensorProduct.assoc ℝ _ _ _).toLinearMap.comp
    (physicalTypeIILeftBentHom q hq hq1 n hn a b c d hbal r).val

theorem physicalTypeIILeftTreeMap_intertwines (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d)
    (z : UqTypeA q n) (v : quantumOccupationSpace ℝ (Fin (n+1)) d) :
    physicalTypeIILeftTreeMap q hq hq1 n hn a b c d hbal r
      (typeAFiniteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n d z v)=
    typeATypeIITriple q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c z
      (physicalTypeIILeftTreeMap q hq hq1 n hn a b c d hbal r v) := by
  unfold physicalTypeIILeftTreeMap
  simp only [LinearMap.comp_apply,LinearEquiv.coe_coe]
  rw [(physicalTypeIILeftBentHom q hq hq1 n hn a b c d hbal r).property]
  exact typeA_associator_intertwines q (ne_of_gt hq) n
    (typeAFiniteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a)
    (typeAFiniteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n b)
    (typeAOppositeSymmetricRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n c) z _

theorem physicalTypeIILeftTreeMap_ne_zero (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d) :
    physicalTypeIILeftTreeMap q hq hq1 n hn a b c d hbal r≠0 := by
  intro hz
  have hb : physicalTypeIILeftBentHom q hq hq1 n hn a b c d hbal r=0 := by
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    apply (TensorProduct.assoc ℝ _ _ _).injective
    have he:=DFunLike.congr_fun hz v
    change (TensorProduct.assoc ℝ _ _ _) ((physicalTypeIILeftBentHom q hq hq1 n hn a b c d hbal r).val v)=0 at he
    simpa only [map_zero,LinearMap.zero_apply] using he
  have hp : physicalTypeIILeftPairHom q hq hq1 n hn a b c d hbal r=0 := by
    apply (oppositeRightHomBending q hq hq1 n c _ _).injective
    simpa only [map_zero] using hb
  exact physicalTypeIILeftPairMap_ne_zero q hq hq1 n hn a b c d hbal r (congrArg Subtype.val hp)

def physicalTypeIILeftHighest (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d) :
    physicalTypeIIHighestSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c d :=
  compactHighestHomEvaluation q n (mixedHighestDynkin n d 0) (symmetricHighestRealization q hq hq1 n d)
    (typeATypeIITriple q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c)
    ⟨physicalTypeIILeftTreeMap q hq hq1 n hn a b c d hbal r,
      physicalTypeIILeftTreeMap_intertwines q hq hq1 n hn a b c d hbal r⟩

theorem physicalTypeIILeftHighest_ne_zero (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d) :
    physicalTypeIILeftHighest q hq hq1 n hn a b c d hbal r≠0 := by
  intro hz
  have hE:=compactHighestHomEvaluation_injective q n (mixedHighestDynkin n d 0)
    (symmetricHighestRealization q hq hq1 n d) (symmetricHighestRealization_channel_top q hq hq1 n d)
    (typeATypeIITriple q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c)
  have h0 : (⟨physicalTypeIILeftTreeMap q hq hq1 n hn a b c d hbal r,
      physicalTypeIILeftTreeMap_intertwines q hq hq1 n hn a b c d hbal r⟩ :
    algebraIntertwinerSpace (typeAFiniteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n d)
      (typeATypeIITriple q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c))=0 := by
    apply hE
    simpa only [map_zero] using hz
  exact physicalTypeIILeftTreeMap_ne_zero q hq hq1 n hn a b c d hbal r (congrArg Subtype.val h0)

end AMSPhysical
#print axioms AMSPhysical.physicalTypeIILeftHighest_ne_zero
