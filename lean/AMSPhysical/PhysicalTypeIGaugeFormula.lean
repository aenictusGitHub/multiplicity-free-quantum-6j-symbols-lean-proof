import AMSTriangleCoordinates

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical

/-- The physical factorial formula for any independently chosen unit channel
families. Only independent row and column signs change with the vertex gauge. -/
theorem physicalTypeI_AMS_Eq35_any_channel_gauge (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h l m c : ℕ) (hadm : m≤l+c)
    (u v : QuantumCupIndex l m c → physicalQuantumHighestMultiplicity q (ne_of_gt hq)
      (qInteger_denominator_ne_zero q hq hq1) (h+1) l m 0 c)
    (hu : ∀ t,u t∈physicalTypeILeftChannelSpace q (ne_of_gt hq)
      (qInteger_denominator_ne_zero q hq hq1) (h+1) l m 0 c t)
    (hv : ∀ t,v t∈physicalTypeIRightChannelSpace q (ne_of_gt hq)
      (qInteger_denominator_ne_zero q hq hq1) (h+1) l m 0 c t)
    (hun : ∀ t,physicalTripleBilin q (h+1) l m c (u t).val (u t).val=1)
    (hvn : ∀ t,physicalTripleBilin q (h+1) l m c (v t).val (v t).val=1) :
    ∃ eps eta : QuantumCupIndex l m c → ℝ,
      (∀ t,eps t=1 ∨ eps t= -1) ∧ (∀ t,eta t=1 ∨ eta t= -1) ∧
      ∀ s t,(-1:ℝ)^(l+c)*physicalTripleBilin q (h+1) l m c (u s).val (v t).val /
        Real.sqrt (mixedIrrepQuantumDimension q hq hq1 (h+1) (by omega) (l-s.val.val) (m-s.val.val)*
          mixedIrrepQuantumDimension q hq hq1 (h+1) (by omega) (c-(m-t.val.val)) t.val.val)=
        eps s*eta t*amsFourTrianglePrefactor q h (l:ℤ) m c (l+c-m)
          (typeILeftLabel l m s.val.val) (typeIRightLabel m c t.val.val)*
        AMSGeneral.kernel (quantumFactorialInt q) h false (l:ℤ) m c (l+c-m)
          (typeILeftLabel l m s.val.val) (typeIRightLabel m c t.val.val) := by
  choose eps heps hU using fun t =>physicalTypeILeftCoupling_unique_sign q hq hq1
    (h+1) (by omega) l m 0 c hadm (Or.inl rfl) t (u t) (hu t) (hun t)
  choose eta heta hV using fun t =>physicalTypeIRightCoupling_unique_sign q hq hq1
    (h+1) (by omega) l m 0 c hadm (Or.inl rfl) t (v t) (hv t) (hvn t)
  refine ⟨eps,eta,heps,heta,?_⟩
  intro s t
  rw [hU s,hV t]
  simp only [Submodule.coe_smul_of_tower,map_smul,LinearMap.smul_apply,smul_eq_mul]
  have hFormula:=physicalTypeI_AMS_Eq35_four_triangles q hq hq1 h l m c hadm s t
  unfold physicalTypeIWignerSymbol at hFormula
  calc
    _ = eps s*eta t*((-1:ℝ)^(l+c)*physicalTripleBilin q (h+1) l m c
      (physicalTypeILeftCoupling q hq hq1 (h+1) (by omega) l m 0 c hadm (Or.inl rfl) s).val
      (physicalTypeIRightCoupling q hq hq1 (h+1) (by omega) l m 0 c hadm (Or.inl rfl) t).val /
        Real.sqrt (mixedIrrepQuantumDimension q hq hq1 (h+1) (by omega) (l-s.val.val) (m-s.val.val)*
          mixedIrrepQuantumDimension q hq hq1 (h+1) (by omega) (c-(m-t.val.val)) t.val.val)) := by ring
    _ = _ := by rw [hFormula];ring

end AMSPhysical
#print axioms AMSPhysical.physicalTypeI_AMS_Eq35_any_channel_gauge
