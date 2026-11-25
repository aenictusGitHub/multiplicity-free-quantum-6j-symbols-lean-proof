import QuantumTypeIILeftPair
import QuantumCupIndependent

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace AMSPhysical

def typeIICommonCupEquiv (a b c d : ℕ) (hbal : a+b=c+d) :
    TypeIICommonIndex a b c d ≃ QuantumCupIndex a c b where
  toFun r:=by
    have hr:=r.isLt
    refine ⟨⟨min a c-r.val,by omega⟩,?_,?_⟩
    · change min a c-r.val≤a
      omega
    · change c-(min a c-r.val)≤b
      omega
  invFun t:=by
    have ht:=t.val.isLt
    have ha:=t.property.1
    have hb:=t.property.2
    exact ⟨min a c-t.val.val,by omega⟩
  left_inv r:=by
    apply Fin.ext
    have hr:=r.isLt
    dsimp only
    omega
  right_inv t:=by
    apply Subtype.ext
    apply Fin.ext
    have ht:=t.val.isLt
    have ha:=t.property.1
    dsimp only
    omega

end AMSPhysical
#print axioms AMSPhysical.typeIICommonCupEquiv
