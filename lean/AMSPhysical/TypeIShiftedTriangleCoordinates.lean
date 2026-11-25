import PhysicalTypeINormalization
import PhysicalWignerFormula

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical

theorem typeILeftShiftedTriangleWeight (q : ℝ) (l m h c : ℕ) (t : QuantumCupIndex l m c) :
    triangleChannelWeight q l (m+h) (quantumCupLeftPath l m h c t).1.val*
      triangleChannelWeight q (coupledLabel l (m+h) (quantumCupLeftPath l m h c t).1) c
        (quantumCupLeftPath l m h c t).2.val=typeILeftShiftedTriangleSq q h l m c t.val.val := by
  have ht:=t.val.isLt
  have hl:=t.property.1
  have hc:=t.property.2
  change triangleChannelWeight q l (m+h) t.val.val*
    triangleChannelWeight q (l+(m+h)-2*t.val.val) c (m-t.val.val)=_
  have h1 : m+h-t.val.val=m-t.val.val+h := by omega
  have h2 : l+(m+h)-2*t.val.val-(m-t.val.val)=l-t.val.val+h := by omega
  have hd1 : l+(m+h)-t.val.val+1=(l-t.val.val)+(m-t.val.val+h)+t.val.val+1 := by omega
  have hd2 : l+(m+h)-2*t.val.val+c-(m-t.val.val)+1=
      (m-t.val.val)+(l-t.val.val+h)+(c-(m-t.val.val))+1 := by omega
  unfold triangleChannelWeight typeILeftShiftedTriangleSq triangleSq
  simp only [Nat.add_zero]
  rw [h1,h2,hd1,hd2]
  ring

theorem typeIRightShiftedTriangleWeight (q : ℝ) (l m h c : ℕ) (t : QuantumCupIndex l m c) :
    triangleChannelWeight q (m+h) c (quantumCupRightPath l m h c t).1.val*
      triangleChannelWeight q l (coupledLabel (m+h) c (quantumCupRightPath l m h c t).1)
        (quantumCupRightPath l m h c t).2.val=typeIRightShiftedTriangleSq q h l m c t.val.val := by
  have ht:=t.val.isLt
  have hl:=t.property.1
  have hc:=t.property.2
  change triangleChannelWeight q (m+h) c (m-t.val.val)*
    triangleChannelWeight q l ((m+h)+c-2*(m-t.val.val)) t.val.val=_
  have h1 : m+h-(m-t.val.val)=t.val.val+h := by omega
  have h2 : m+h+c-2*(m-t.val.val)-t.val.val=c-(m-t.val.val)+h := by omega
  have hd1 : m+h+c-(m-t.val.val)+1=(c-(m-t.val.val))+(t.val.val+h)+(m-t.val.val)+1 := by omega
  have hd2 : l+(m+h+c-2*(m-t.val.val))-t.val.val+1=
      t.val.val+(c-(m-t.val.val)+h)+(l-t.val.val)+1 := by omega
  unfold triangleChannelWeight typeIRightShiftedTriangleSq triangleSq
  simp only [Nat.add_zero]
  rw [h1,h2,hd1,hd2]
  ring

theorem typeIShifted_wignerTrianglePrefactor (q : ℝ) (l m h c : ℕ) (s t : QuantumCupIndex l m c) :
    wignerTrianglePrefactor q l (m+h) c (quantumCupLeftPath l m h c s) (quantumCupRightPath l m h c t)=
      Real.sqrt (typeILeftShiftedTriangleSq q h l m c s.val.val*typeIRightShiftedTriangleSq q h l m c t.val.val) := by
  unfold wignerTrianglePrefactor
  rw [mul_assoc,typeILeftShiftedTriangleWeight,typeIRightShiftedTriangleWeight]

end AMSPhysical
#print axioms AMSPhysical.typeIShifted_wignerTrianglePrefactor
