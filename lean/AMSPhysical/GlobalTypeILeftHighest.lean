import GlobalTypeILeftFixedChannel
import PhysicalTypeIHighestTreeEmbedding
import GlobalTypeIIRightVertices

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 300000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def globalTypeILeftHighest (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h p s c d : ℕ) (hbal : p+c=s+d) (hs : s≤c) (r : ℕ) :
    physicalTypeIHighestSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      (h+1) (p+r) (s+r) c d :=
  ⟨(globalTypeILeftVector q hq hq1 h p s c r hs).val,by
  have he:=(mem_typeAHighestSpace q (h+1) _ _
    (globalTypeILeftVector q hq hq1 h p s c r hs).val).mp
      (globalTypeILeftVector q hq hq1 h p s c r hs).property
  have hd : (p+r)+c-(s+r)+0=d := by omega
  apply (mem_typeAHighestSpace q (h+1) _ _ _).mpr
  refine ⟨he.1,?_⟩
  intro i
  have hk:=he.2 i
  change _=q^(mixedHighestDynkin (h+1) ((p+r)+c-(s+r)+0) 0 i) • _ at hk
  rw [hd] at hk
  exact hk⟩

end AMSPhysical
#print axioms AMSPhysical.globalTypeILeftHighest
