import PhysicalTypeIAMSFormula

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical

def amsThetaSq (q : ℝ) (h : ℕ) (a b c : ℤ) : ℝ :=
  quantumFactorialInt q ((a+b-c)/2)*quantumFactorialInt q ((a+c-b)/2)*quantumFactorialInt q ((b+c-a)/2)/
    quantumFactorialInt q ((a+b+c)/2+h+1)

def amsFourTrianglePrefactor (q : ℝ) (h : ℕ) (a b c d i j : ℤ) : ℝ :=
  factorialConstant (qfactorial q) h * Real.sqrt
    (amsThetaSq q h a b i*amsThetaSq q h c d i*amsThetaSq q h a d j*amsThetaSq q h b c j)

theorem amsThetaSq_coordinates (q : ℝ) (h p r u : ℕ) :
    amsThetaSq q h ((p+u:ℕ):ℤ) ((r+u:ℕ):ℤ) ((p+r:ℕ):ℤ)=triangleSq (qfactorial q) h p r u := by
  have h1 : (((p+u:ℕ):ℤ)+((r+u:ℕ):ℤ)-((p+r:ℕ):ℤ))/2=(u:ℤ) := by omega
  have h2 : (((p+u:ℕ):ℤ)+((p+r:ℕ):ℤ)-((r+u:ℕ):ℤ))/2=(p:ℤ) := by omega
  have h3 : (((r+u:ℕ):ℤ)+((p+r:ℕ):ℤ)-((p+u:ℕ):ℤ))/2=(r:ℤ) := by omega
  have h4 : (((p+u:ℕ):ℤ)+((r+u:ℕ):ℤ)+((p+r:ℕ):ℤ))/2+(h:ℤ)+1=((p+r+u+h+1:ℕ):ℤ) := by omega
  unfold amsThetaSq
  rw [h1,h2,h3,h4]
  simp only [quantumFactorialInt,Int.toNat_natCast]
  rfl

theorem amsThetaSq_swap (q : ℝ) (h : ℕ) (a b c : ℤ) : amsThetaSq q h a b c=amsThetaSq q h b a c := by
  have h1 : (a+b-c)/2=(b+a-c)/2 := by omega
  have h2 : (a+b+c)/2=(b+a+c)/2 := by omega
  unfold amsThetaSq
  rw [h1,h2]
  ring

theorem typeI_left_first_theta (q : ℝ) (h l m c : ℕ) (s : QuantumCupIndex l m c) :
    amsThetaSq q h (l:ℤ) m (typeILeftLabel l m s.val.val)=
      triangleSq (qfactorial q) h (l-s.val.val) (m-s.val.val) s.val.val := by
  have hs:=s.val.isLt
  have hl:=s.property.1
  have he:=amsThetaSq_coordinates q h (l-s.val.val) (m-s.val.val) s.val.val
  rw [show (((l-s.val.val)+s.val.val:ℕ):ℤ)=(l:ℤ) from by omega,
    show (((m-s.val.val)+s.val.val:ℕ):ℤ)=(m:ℤ) from by omega] at he
  exact he

theorem typeI_left_second_theta (q : ℝ) (h l m c : ℕ) (hadm : m≤l+c) (s : QuantumCupIndex l m c) :
    amsThetaSq q h (c:ℤ) (l+c-m) (typeILeftLabel l m s.val.val)=
      triangleSq (qfactorial q) h (m-s.val.val) (l-s.val.val) (c-(m-s.val.val)) := by
  have hs:=s.val.isLt
  have hl:=s.property.1
  have hc:=s.property.2
  have he:=amsThetaSq_coordinates q h (m-s.val.val) (l-s.val.val) (c-(m-s.val.val))
  rw [show (((m-s.val.val)+(c-(m-s.val.val)):ℕ):ℤ)=(c:ℤ) from by omega,
    show (((l-s.val.val)+(c-(m-s.val.val)):ℕ):ℤ)=(l:ℤ)+(c:ℤ)-(m:ℤ) from by omega,
    show (((m-s.val.val)+(l-s.val.val):ℕ):ℤ)=(typeILeftLabel l m s.val.val:ℤ) from by unfold typeILeftLabel;omega] at he
  exact he

theorem typeI_right_first_theta (q : ℝ) (h l m c : ℕ) (t : QuantumCupIndex l m c) :
    amsThetaSq q h (m:ℤ) c (typeIRightLabel m c t.val.val)=
      triangleSq (qfactorial q) h (c-(m-t.val.val)) t.val.val (m-t.val.val) := by
  have ht:=t.val.isLt
  have hc:=t.property.2
  rw [amsThetaSq_swap]
  have he:=amsThetaSq_coordinates q h (c-(m-t.val.val)) t.val.val (m-t.val.val)
  rw [show (((c-(m-t.val.val))+(m-t.val.val):ℕ):ℤ)=(c:ℤ) from by omega,
    show ((t.val.val+(m-t.val.val):ℕ):ℤ)=(m:ℤ) from by omega] at he
  exact he

theorem typeI_right_second_theta (q : ℝ) (h l m c : ℕ) (hadm : m≤l+c) (t : QuantumCupIndex l m c) :
    amsThetaSq q h (l:ℤ) (l+c-m) (typeIRightLabel m c t.val.val)=
      triangleSq (qfactorial q) h t.val.val (c-(m-t.val.val)) (l-t.val.val) := by
  have ht:=t.val.isLt
  have hl:=t.property.1
  have hc:=t.property.2
  have he:=amsThetaSq_coordinates q h t.val.val (c-(m-t.val.val)) (l-t.val.val)
  rw [show ((t.val.val+(l-t.val.val):ℕ):ℤ)=(l:ℤ) from by omega,
    show (((c-(m-t.val.val))+(l-t.val.val):ℕ):ℤ)=(l:ℤ)+(c:ℤ)-(m:ℤ) from by omega,
    show ((t.val.val+(c-(m-t.val.val)):ℕ):ℤ)=(typeIRightLabel m c t.val.val:ℤ) from by unfold typeIRightLabel;omega] at he
  exact he

theorem typeIAMSPrefactor_four_triangles (q : ℝ) (h l m c : ℕ) (hadm : m≤l+c) (s t : QuantumCupIndex l m c) :
    typeIAMSPrefactor q h l m c s.val.val t.val.val=
      amsFourTrianglePrefactor q h (l:ℤ) m c (l+c-m)
        (typeILeftLabel l m s.val.val) (typeIRightLabel m c t.val.val) := by
  unfold typeIAMSPrefactor amsFourTrianglePrefactor
  rw [typeI_left_first_theta,typeI_left_second_theta q h l m c hadm,
    typeI_right_second_theta q h l m c hadm,typeI_right_first_theta]
  unfold typeILeftTriangleSq typeIRightTriangleSq
  congr 2
  ring

/-- Literal four-triangle form of the positive-real Type-I physical AMS identity. -/
theorem physicalTypeI_AMS_Eq35_four_triangles (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h l m c : ℕ) (hadm : m≤l+c) (s t : QuantumCupIndex l m c) :
    physicalTypeIWignerSymbol q hq hq1 h l m c hadm s t=
      amsFourTrianglePrefactor q h (l:ℤ) m c (l+c-m)
        (typeILeftLabel l m s.val.val) (typeIRightLabel m c t.val.val)*
      AMSGeneral.kernel (quantumFactorialInt q) h false (l:ℤ) m c (l+c-m)
        (typeILeftLabel l m s.val.val) (typeIRightLabel m c t.val.val) := by
  rw [physicalTypeI_AMS_Eq35,typeIAMSPrefactor_four_triangles q h l m c hadm]

end AMSPhysical
#print axioms AMSPhysical.typeIAMSPrefactor_four_triangles
