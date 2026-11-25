import AMSTriangleCoordinates
import PhysicalTypeIIPrefactor
import TypeIIShiftedPaths

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

theorem typeII_left_first_theta (q : ℝ) (h a b c d : ℕ) (r : TypeIICommonIndex a b c d) :
    amsThetaSq q h (a:ℤ) b (typeIILeftLabel a b r.val)=triangleSq (qfactorial q) h (a-r.val) (b-r.val) r.val := by
  have hr:=r.isLt
  have he:=amsThetaSq_coordinates q h (a-r.val) (b-r.val) r.val
  rw [show (((a-r.val)+r.val:ℕ):ℤ)=(a:ℤ) from by omega,
    show (((b-r.val)+r.val:ℕ):ℤ)=(b:ℤ) from by omega] at he
  exact he

theorem typeII_left_second_theta (q : ℝ) (h a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d) :
    amsThetaSq q h (c:ℤ) d (typeIILeftLabel a b r.val)=triangleSq (qfactorial q) h (c-r.val) (d-r.val) r.val := by
  have hr:=r.isLt
  have he:=amsThetaSq_coordinates q h (c-r.val) (d-r.val) r.val
  rw [show (((c-r.val)+r.val:ℕ):ℤ)=(c:ℤ) from by omega,
    show (((d-r.val)+r.val:ℕ):ℤ)=(d:ℤ) from by omega,
    show (((c-r.val)+(d-r.val):ℕ):ℤ)=(typeIILeftLabel a b r.val:ℤ) from by unfold typeIILeftLabel;omega] at he
  exact he

theorem typeII_right_first_theta (q : ℝ) (h a b c : ℕ) (t : QuantumCupIndex a c b) :
    amsThetaSq q h (b:ℤ) c (typeIIRightLabel b c t.val.val)=
      triangleSq (qfactorial q) h t.val.val (b-(c-t.val.val)) (c-t.val.val) := by
  have ht:=t.val.isLt
  have hb:=t.property.2
  rw [amsThetaSq_swap]
  have he:=amsThetaSq_coordinates q h t.val.val (b-(c-t.val.val)) (c-t.val.val)
  rw [show ((t.val.val+(c-t.val.val):ℕ):ℤ)=(c:ℤ) from by omega,
    show (((b-(c-t.val.val))+(c-t.val.val):ℕ):ℤ)=(b:ℤ) from by omega,
    show ((t.val.val+(b-(c-t.val.val)):ℕ):ℤ)=(typeIIRightLabel b c t.val.val:ℤ) from by unfold typeIIRightLabel;omega] at he
  exact he

theorem typeII_right_second_theta (q : ℝ) (h a b c d : ℕ) (hbal : a+b=c+d) (t : QuantumCupIndex a c b) :
    amsThetaSq q h (a:ℤ) d (typeIIRightLabel b c t.val.val)=
      triangleSq (qfactorial q) h (b-(c-t.val.val)) t.val.val (a-t.val.val) := by
  have ht:=t.val.isLt
  have ha:=t.property.1
  have hb:=t.property.2
  rw [amsThetaSq_swap]
  have he:=amsThetaSq_coordinates q h (b-(c-t.val.val)) t.val.val (a-t.val.val)
  rw [show (((b-(c-t.val.val))+(a-t.val.val):ℕ):ℤ)=(d:ℤ) from by omega,
    show ((t.val.val+(a-t.val.val):ℕ):ℤ)=(a:ℤ) from by omega] at he
  exact he

theorem typeIIAMSPrefactor_four_triangles (q : ℝ) (h a b c d : ℕ) (hbal : a+b=c+d)
    (r : TypeIICommonIndex a b c d) (t : QuantumCupIndex a c b) :
    typeIIAMSPrefactor q h a b c d r.val t.val.val=
      amsFourTrianglePrefactor q h (a:ℤ) b c d (typeIILeftLabel a b r.val) (typeIIRightLabel b c t.val.val) := by
  unfold typeIIAMSPrefactor amsFourTrianglePrefactor
  rw [typeII_left_first_theta,typeII_left_second_theta q h a b c d hbal,
    typeII_right_second_theta q h a b c d hbal,typeII_right_first_theta]
  unfold typeIILeftTriangleSq typeIIRightTriangleSq
  congr 2
  ring

end AMSPhysical
#print axioms AMSPhysical.typeIIAMSPrefactor_four_triangles
