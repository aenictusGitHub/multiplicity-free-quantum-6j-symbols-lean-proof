import PhysicalTypeIRankReduction
import PhysicalTypeIAMSLabels
import QuantumTripleChannelsActual

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical

/-- The higher-rank physical Type-I Wigner coefficient in the transported
channel phase convention. Its numerator is an actual compact tensor-space
overlap and its two dimensions are actual restricted pivotal traces.
No factorial candidate is used to define this coefficient. -/
def physicalTypeIWignerSymbol (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h l m c : ℕ) (hadm : m≤l+c) (s t : QuantumCupIndex l m c) : ℝ :=
  (-1:ℝ)^(l+c)*physicalTripleBilin q (h+1) l m c
    (physicalTypeILeftCoupling q hq hq1 (h+1) (by omega) l m 0 c hadm (Or.inl rfl) s).val
    (physicalTypeIRightCoupling q hq hq1 (h+1) (by omega) l m 0 c hadm (Or.inl rfl) t).val /
      Real.sqrt (mixedIrrepQuantumDimension q hq hq1 (h+1) (by omega) (l-s.val.val) (m-s.val.val)*
        mixedIrrepQuantumDimension q hq hq1 (h+1) (by omega) (c-(m-t.val.val)) t.val.val)

/-- Physical Type-I AMS Eq. (35), for every rank N=h+2 and every admissible
exterior/channel label, at positive real q != 1. The exact factorial sum,
positive normalization and global sign are conclusions. Type II and generic
complex continuation are not asserted by this theorem. -/
theorem physicalTypeI_AMS_Eq35 (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h l m c : ℕ) (hadm : m≤l+c) (s t : QuantumCupIndex l m c) :
    physicalTypeIWignerSymbol q hq hq1 h l m c hadm s t=
      typeIAMSPrefactor q h l m c s.val.val t.val.val*
        AMSGeneral.kernel (quantumFactorialInt q) h false (l:ℤ) m c (l+c-m)
          (typeILeftLabel l m s.val.val) (typeIRightLabel m c t.val.val) := by
  unfold physicalTypeIWignerSymbol
  have hOverlap:=physicalTypeICoupling_overlap_rankTwo q hq hq1 (h+1) (by omega) l m 0 c hadm (Or.inl rfl) s t
  rw [show 0+(h+1)-1=h from by omega] at hOverlap
  simp only [Nat.add_zero] at hOverlap
  rw [hOverlap]
  rw [← mixedWeyl_actual_dimension q hq hq1 h (l-s.val.val) (m-s.val.val),
    ← mixedWeyl_actual_dimension q hq hq1 h (c-(m-t.val.val)) t.val.val]
  change (-1:ℝ)^(l+c)*quantumRacahMatrix q hq hq1 l (m+h) c
    (quantumCupLeftPath l m h c s) (quantumCupRightPath l m h c t)/
    Real.sqrt (typeILeftDimension q h l m s.val.val*typeIRightDimension q h m c t.val.val)=_
  rw [typeIShifted_physicalRacah_kernel q hq hq1 h l m c hadm s t]
  have hNorm:=typeINormalization_prefactor q hq h l m c s.val.val t.val.val
  change Real.sqrt (qnum q (typeILeftLabel l m s.val.val+h+1)*qnum q (typeIRightLabel m c t.val.val+h+1))*
    Real.sqrt (typeILeftShiftedTriangleSq q h l m c s.val.val*typeIRightShiftedTriangleSq q h l m c t.val.val)/
    Real.sqrt (typeILeftDimension q h l m s.val.val*typeIRightDimension q h m c t.val.val)=_ at hNorm
  calc
    _ = ((-1:ℝ)^(l+c)*(-1:ℝ)^(l+c))*
      (Real.sqrt (qnum q (typeILeftLabel l m s.val.val+h+1)*qnum q (typeIRightLabel m c t.val.val+h+1))*
        Real.sqrt (typeILeftShiftedTriangleSq q h l m c s.val.val*typeIRightShiftedTriangleSq q h l m c t.val.val)/
        Real.sqrt (typeILeftDimension q h l m s.val.val*typeIRightDimension q h m c t.val.val))*
      AMSGeneral.kernel (quantumFactorialInt q) h false (l:ℤ) m c (l+c-m)
        (typeILeftLabel l m s.val.val) (typeIRightLabel m c t.val.val) := by ring
    _ = _ := by rw [AMSGeneral.sign_square,one_mul,hNorm]

end AMSPhysical
#print axioms AMSPhysical.physicalTypeI_AMS_Eq35
