import TypeIShiftedTriangleCoordinates
import PhysicalTypeIPrefactor

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical

def typeILeftLabel (l m t : ℕ) : ℕ := (l-t)+(m-t)
def typeIRightLabel (m c t : ℕ) : ℕ := (c-(m-t))+t

theorem typeILeftShifted_label (l m h c : ℕ) (t : QuantumCupIndex l m c) :
    coupledLabel l (m+h) (quantumCupLeftPath l m h c t).1=typeILeftLabel l m t.val.val+h := by
  have ht:=t.val.isLt
  have hl:=t.property.1
  unfold coupledLabel typeILeftLabel quantumCupLeftPath
  simp only
  omega

theorem typeIRightShifted_label (l m h c : ℕ) (t : QuantumCupIndex l m c) :
    coupledLabel (m+h) c (quantumCupRightPath l m h c t).1=typeIRightLabel m c t.val.val+h := by
  have ht:=t.val.isLt
  have hc:=t.property.2
  unfold coupledLabel typeIRightLabel quantumCupRightPath
  simp only
  omega

theorem typeIShifted_kernel (F : ℤ → ℝ) (h l m c : ℕ) (s t : QuantumCupIndex l m c) :
    AMSGeneral.kernel F 0 false (l:ℤ) (m+h) c (l+c-m+h)
      (coupledLabel l (m+h) (quantumCupLeftPath l m h c s).1)
      (coupledLabel (m+h) c (quantumCupRightPath l m h c t).1)=
      (-1:ℝ)^h*AMSGeneral.kernel F h false (l:ℤ) m c (l+c-m)
        (typeILeftLabel l m s.val.val) (typeIRightLabel m c t.val.val) := by
  rw [typeILeftShifted_label,typeIRightShifted_label]
  simp only [Nat.cast_add]
  exact AMSGeneral.shifted_kernel_typeI F h (l:ℤ) m c (l+c-m)
    (typeILeftLabel l m s.val.val) (typeIRightLabel m c t.val.val)

theorem typeIShifted_defect (l m h c : ℕ) (hadm : m≤l+c) (s : QuantumCupIndex l m c) :
    leftHighestDefect l (m+h) c (l+c-m+h)=m := by
  have he:=fixedLeftHighest_defect l (m+h) c (l+c-m+h) (quantumCupFixedLeftPath l m h c hadm s)
  change s.val.val+(m-s.val.val)=leftHighestDefect l (m+h) c (l+c-m+h) at he
  have hs:=s.val.isLt
  omega

/-- The physical standard sl2 overlap has the higher-rank AMS scalar kernel,
with its full positive rank-two normalization and the source global sign. -/
theorem typeIShifted_physicalRacah_kernel (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h l m c : ℕ) (hadm : m≤l+c) (s t : QuantumCupIndex l m c) :
    quantumRacahMatrix q hq hq1 l (m+h) c (quantumCupLeftPath l m h c s) (quantumCupRightPath l m h c t)=
      (-1:ℝ)^(l+c)*Real.sqrt (qnum q (typeILeftLabel l m s.val.val+h+1)*qnum q (typeIRightLabel m c t.val.val+h+1))*
        Real.sqrt (typeILeftShiftedTriangleSq q h l m c s.val.val*typeIRightShiftedTriangleSq q h l m c t.val.val)*
          AMSGeneral.kernel (quantumFactorialInt q) h false (l:ℤ) m c (l+c-m)
            (typeILeftLabel l m s.val.val) (typeIRightLabel m c t.val.val) := by
  have he:=physical_rank_two_AMS_standard q hq hq1 l (m+h) c (l+c-m+h)
    (quantumCupFixedLeftPath l m h c hadm s) (quantumCupRightPath l m h c t)
    (quantumCupRightPath_total l m h c hadm t)
  rw [typeIShifted_defect l m h c hadm s] at he
  dsimp only [quantumCupFixedLeftPath] at he
  have hp : l+(m+h)+c-m=l+c+h := by omega
  rw [hp,standardRacahPrefactor_dimensions q hq,typeIShifted_wignerTrianglePrefactor] at he
  have hd : ((l+c-m+h:ℕ):ℤ)=(l:ℤ)+(c:ℤ)-(m:ℤ)+(h:ℤ) := by omega
  rw [hd] at he
  simp only [Nat.cast_add] at he
  rw [typeIShifted_kernel,typeILeftShifted_label,typeIRightShifted_label,pow_add] at he
  have hs:=AMSGeneral.sign_square (𝕂:=ℝ) h
  calc
    _ = _ := he
    _ = _ := by
      calc
        _ = ((-1:ℝ)^h*(-1:ℝ)^h)*((-1:ℝ)^(l+c)*
          Real.sqrt (qnum q (typeILeftLabel l m s.val.val+h+1)*qnum q (typeIRightLabel m c t.val.val+h+1))*
          Real.sqrt (typeILeftShiftedTriangleSq q h l m c s.val.val*typeIRightShiftedTriangleSq q h l m c t.val.val)*
          AMSGeneral.kernel (quantumFactorialInt q) h false (l:ℤ) m c (l+c-m)
            (typeILeftLabel l m s.val.val) (typeIRightLabel m c t.val.val)) := by ring
        _ = _ := by rw [hs,one_mul]

end AMSPhysical
#print axioms AMSPhysical.typeIShifted_physicalRacah_kernel
