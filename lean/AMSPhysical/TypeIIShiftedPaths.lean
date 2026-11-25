import PhysicalTypeIINormalization
import QuantumFusionHighest
import QuantumFixedHighest

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

def typeIILeftLabel (a b r : ℕ) : ℕ:=(a-r)+(b-r)
def typeIIRightLabel (b c t : ℕ) : ℕ:=(b-(c-t))+t

def typeIIShiftedLeftPath (h a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d) :
    LeftHighestPath (a+h) (b+h) c := by
  have hr:=r.isLt
  refine ⟨⟨r.val+h,by omega⟩,⟨c-r.val,?_⟩⟩
  unfold coupledLabel
  simp only
  omega

def typeIIShiftedRightPath (h a b c : ℕ) (t : QuantumCupIndex a c b) :
    RightHighestPath (a+h) (b+h) c := by
  have ht:=t.val.isLt
  have ha:=t.property.1
  have hb:=t.property.2
  refine ⟨⟨c-t.val.val,by omega⟩,⟨t.val.val+h,?_⟩⟩
  unfold coupledLabel
  simp only
  omega

theorem typeIIShiftedLeft_label (h a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d) :
    coupledLabel (a+h) (b+h) (typeIIShiftedLeftPath h a b c d hbal r).1=typeIILeftLabel a b r.val := by
  have hr:=r.isLt
  unfold coupledLabel typeIILeftLabel typeIIShiftedLeftPath
  simp only
  omega

theorem typeIIShiftedRight_label (h a b c : ℕ) (t : QuantumCupIndex a c b) :
    coupledLabel (b+h) c (typeIIShiftedRightPath h a b c t).1=typeIIRightLabel b c t.val.val+h := by
  have ht:=t.val.isLt
  have hb:=t.property.2
  unfold coupledLabel typeIIRightLabel typeIIShiftedRightPath
  simp only
  omega

theorem typeIIShiftedLeft_total (h a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d) :
    leftTotalLabel (a+h) (b+h) c (typeIIShiftedLeftPath h a b c d hbal r)=d := by
  have he:=leftTotalLabel_defect (a+h) (b+h) c (typeIIShiftedLeftPath h a b c d hbal r)
  have hr:=r.isLt
  change a+h+(b+h)+c=leftTotalLabel (a+h) (b+h) c (typeIIShiftedLeftPath h a b c d hbal r)+2*((r.val+h)+(c-r.val)) at he
  omega

theorem typeIIShiftedRight_total (h a b c d : ℕ) (hbal : a+b=c+d) (t : QuantumCupIndex a c b) :
    rightTotalLabel (a+h) (b+h) c (typeIIShiftedRightPath h a b c t)=d := by
  have he:=rightTotalLabel_defect (a+h) (b+h) c (typeIIShiftedRightPath h a b c t)
  have ht:=t.val.isLt
  change a+h+(b+h)+c=rightTotalLabel (a+h) (b+h) c (typeIIShiftedRightPath h a b c t)+2*((c-t.val.val)+(t.val.val+h)) at he
  omega

def typeIIShiftedFixedLeftPath (h a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d) :
    FixedLeftHighest (a+h) (b+h) c d :=
  ⟨typeIIShiftedLeftPath h a b c d hbal r,typeIIShiftedLeft_total h a b c d hbal r⟩

theorem typeIIShifted_defect (h a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d) :
    leftHighestDefect (a+h) (b+h) c d=c+h := by
  have he:=fixedLeftHighest_defect (a+h) (b+h) c d (typeIIShiftedFixedLeftPath h a b c d hbal r)
  have hr:=r.isLt
  change (r.val+h)+(c-r.val)=leftHighestDefect (a+h) (b+h) c d at he
  omega

end AMSPhysical
#print axioms AMSPhysical.typeIIShiftedLeft_total
#print axioms AMSPhysical.typeIIShiftedRight_total
