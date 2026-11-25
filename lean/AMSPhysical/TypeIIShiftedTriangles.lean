import TypeIIShiftedPaths
import PhysicalWignerFormula

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

theorem typeIIShiftedLeftTriangleWeight (q : ℝ) (h a b c d : ℕ) (hbal : a+b=c+d)
    (r : TypeIICommonIndex a b c d) :
    triangleChannelWeight q (a+h) (b+h) (typeIIShiftedLeftPath h a b c d hbal r).1.val*
      triangleChannelWeight q (coupledLabel (a+h) (b+h) (typeIIShiftedLeftPath h a b c d hbal r).1) c
        (typeIIShiftedLeftPath h a b c d hbal r).2.val=typeIILeftShiftedTriangleSq q h a b c d r.val := by
  have hr:=r.isLt
  change triangleChannelWeight q (a+h) (b+h) (r.val+h)*
    triangleChannelWeight q ((a+h)+(b+h)-2*(r.val+h)) c (c-r.val)=_
  have hi : (a+h)+(b+h)-2*(r.val+h)=(a-r.val)+(b-r.val) := by omega
  rw [hi]
  have h1 : a+h-(r.val+h)=a-r.val := by omega
  have h2 : b+h-(r.val+h)=b-r.val := by omega
  have h3 : (a-r.val)+(b-r.val)-(c-r.val)=d-r.val := by omega
  have h4 : c-(c-r.val)=r.val := by omega
  have hd1 : a+h+(b+h)-(r.val+h)+1=(a-r.val)+(b-r.val)+(r.val+h)+1 := by omega
  have hd2 : (a-r.val)+(b-r.val)+c-(c-r.val)+1=(c-r.val)+(d-r.val)+r.val+1 := by omega
  unfold triangleChannelWeight typeIILeftShiftedTriangleSq triangleSq
  simp only [Nat.add_zero]
  rw [h1,h2,h3,h4,hd1,hd2]
  ring

theorem typeIIShiftedRightTriangleWeight (q : ℝ) (h a b c : ℕ) (t : QuantumCupIndex a c b) :
    triangleChannelWeight q (b+h) c (typeIIShiftedRightPath h a b c t).1.val*
      triangleChannelWeight q (a+h) (coupledLabel (b+h) c (typeIIShiftedRightPath h a b c t).1)
        (typeIIShiftedRightPath h a b c t).2.val=typeIIRightShiftedTriangleSq q h a b c t.val.val := by
  have ht:=t.val.isLt
  have ha:=t.property.1
  have hb:=t.property.2
  change triangleChannelWeight q (b+h) c (c-t.val.val)*
    triangleChannelWeight q (a+h) ((b+h)+c-2*(c-t.val.val)) (t.val.val+h)=_
  have h1 : b+h-(c-t.val.val)=b-(c-t.val.val)+h := by omega
  have h2 : c-(c-t.val.val)=t.val.val := by omega
  have h3 : a+h-(t.val.val+h)=a-t.val.val := by omega
  have h4 : b+h+c-2*(c-t.val.val)-(t.val.val+h)=b-(c-t.val.val) := by omega
  have hd1 : b+h+c-(c-t.val.val)+1=t.val.val+(b-(c-t.val.val)+h)+(c-t.val.val)+1 := by omega
  have hd2 : a+h+(b+h+c-2*(c-t.val.val))-(t.val.val+h)+1=
      (b-(c-t.val.val))+(t.val.val+h)+(a-t.val.val)+1 := by omega
  unfold triangleChannelWeight typeIIRightShiftedTriangleSq triangleSq
  simp only [Nat.add_zero]
  rw [h1,h2,h3,h4,hd1,hd2]
  ring

theorem typeIIShifted_wignerTrianglePrefactor (q : ℝ) (h a b c d : ℕ) (hbal : a+b=c+d)
    (r : TypeIICommonIndex a b c d) (t : QuantumCupIndex a c b) :
    wignerTrianglePrefactor q (a+h) (b+h) c (typeIIShiftedLeftPath h a b c d hbal r)
      (typeIIShiftedRightPath h a b c t)=
      Real.sqrt (typeIILeftShiftedTriangleSq q h a b c d r.val*typeIIRightShiftedTriangleSq q h a b c t.val.val) := by
  unfold wignerTrianglePrefactor
  rw [mul_assoc,typeIIShiftedLeftTriangleWeight,typeIIShiftedRightTriangleWeight]

end AMSPhysical
#print axioms AMSPhysical.typeIIShifted_wignerTrianglePrefactor
