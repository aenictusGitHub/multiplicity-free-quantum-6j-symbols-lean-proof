import QuantumCupIndependent
import QuantumFixedHighest
import QuantumBoundaryRecoupling

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
noncomputable section
namespace AMSPhysical

def quantumCupLeftPath (l m b c : ℕ) (t : QuantumCupIndex l m c) : LeftHighestPath l (m+b) c := by
  have ht:=t.val.isLt
  have hl:=t.property.1
  have hc:=t.property.2
  refine ⟨⟨t.val.val,by omega⟩,⟨m-t.val.val,?_⟩⟩
  unfold coupledLabel
  simp only
  omega

def quantumCupRightPath (l m b c : ℕ) (t : QuantumCupIndex l m c) : RightHighestPath l (m+b) c := by
  have ht:=t.val.isLt
  have hl:=t.property.1
  have hc:=t.property.2
  refine ⟨⟨m-t.val.val,by omega⟩,⟨t.val.val,?_⟩⟩
  unfold coupledLabel
  simp only
  omega

theorem quantumCupLeftPath_total (l m b c : ℕ) (hadm : m≤l+c) (t : QuantumCupIndex l m c) :
    leftTotalLabel l (m+b) c (quantumCupLeftPath l m b c t)=l+c-m+b := by
  have he:=leftTotalLabel_defect l (m+b) c (quantumCupLeftPath l m b c t)
  have ht:=t.val.isLt
  change l+(m+b)+c=leftTotalLabel l (m+b) c (quantumCupLeftPath l m b c t)+2*(t.val.val+(m-t.val.val)) at he
  omega

theorem quantumCupRightPath_total (l m b c : ℕ) (hadm : m≤l+c) (t : QuantumCupIndex l m c) :
    rightTotalLabel l (m+b) c (quantumCupRightPath l m b c t)=l+c-m+b := by
  have he:=rightTotalLabel_defect l (m+b) c (quantumCupRightPath l m b c t)
  have ht:=t.val.isLt
  change l+(m+b)+c=rightTotalLabel l (m+b) c (quantumCupRightPath l m b c t)+2*((m-t.val.val)+t.val.val) at he
  omega

def quantumCupFixedLeftPath (l m b c : ℕ) (hadm : m≤l+c) (t : QuantumCupIndex l m c) :
    FixedLeftHighest l (m+b) c (l+c-m+b) :=
  ⟨quantumCupLeftPath l m b c t,quantumCupLeftPath_total l m b c hadm t⟩

theorem quantumCupLeftPath_intermediate (l m b c : ℕ) (t : QuantumCupIndex l m c) :
    coupledLabel l (m+b) (quantumCupLeftPath l m b c t).1=l+m+b-2*t.val.val := by
  unfold coupledLabel quantumCupLeftPath
  simp only
  omega

theorem quantumCupRightPath_intermediate (l m b c : ℕ) (t : QuantumCupIndex l m c) :
    coupledLabel (m+b) c (quantumCupRightPath l m b c t).1=m+b+c-2*(m-t.val.val) := rfl

end AMSPhysical
#print axioms AMSPhysical.quantumCupLeftPath_total
#print axioms AMSPhysical.quantumCupRightPath_total
