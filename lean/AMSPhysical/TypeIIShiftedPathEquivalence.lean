import TypeIIShiftedPaths

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical

/-- The shifted standard paths exhaust the fixed total highest space. -/
def typeIIShiftedLeftPathEquiv (h a b c d:ℕ) (hbal:a+b=c+d):
    TypeIICommonIndex a b c d ≃ FixedLeftHighest (a+h) (b+h) c d where
  toFun:=typeIIShiftedFixedLeftPath h a b c d hbal
  invFun p:=by
    have hp:=leftTotalLabel_defect (a+h) (b+h) c p.val
    rw [p.property] at hp
    have hs:=channel_right_bound (coupledLabel (a+h) (b+h) p.val.1) c p.val.2
    have ha:=channel_left_bound (a+h) (b+h) p.val.1
    have hb:=channel_right_bound (a+h) (b+h) p.val.1
    have hi:=channel_left_bound (coupledLabel (a+h) (b+h) p.val.1) c p.val.2
    unfold coupledLabel at hi
    change a+h+(b+h)+c=d+2*(p.val.1.val+p.val.2.val) at hp
    refine ⟨p.val.1.val-h,?_⟩
    change p.val.1.val-h < min (min a b) (min c d)+1
    omega
  left_inv r:=by
    apply Fin.ext
    change r.val+h-h=r.val
    omega
  right_inv p:=by
    apply fixedLeftHighest_index_injective (a+h) (b+h) c d
    change p.val.1.val-h+h=p.val.1.val
    have hp:=leftTotalLabel_defect (a+h) (b+h) c p.val
    rw [p.property] at hp
    have hs:=channel_right_bound (coupledLabel (a+h) (b+h) p.val.1) c p.val.2
    change a+h+(b+h)+c=d+2*(p.val.1.val+p.val.2.val) at hp
    omega

end AMSPhysical
#print axioms AMSPhysical.typeIIShiftedLeftPathEquiv
