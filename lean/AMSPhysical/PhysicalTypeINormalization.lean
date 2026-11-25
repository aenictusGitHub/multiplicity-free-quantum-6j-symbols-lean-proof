import Normalization
import QuantumMixedDimensionClosed
import QuantumCupFusionPaths

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical

def typeILeftTriangleSq (q : ℝ) (h l m c t : ℕ) : ℝ :=
  triangleSq (qfactorial q) h (l-t) (m-t) t *
    triangleSq (qfactorial q) h (m-t) (l-t) (c-(m-t))

def typeIRightTriangleSq (q : ℝ) (h l m c t : ℕ) : ℝ :=
  triangleSq (qfactorial q) h (c-(m-t)) t (m-t) *
    triangleSq (qfactorial q) h t (c-(m-t)) (l-t)

def typeILeftShiftedTriangleSq (q : ℝ) (h l m c t : ℕ) : ℝ :=
  triangleSq (qfactorial q) 0 (l-t) (m-t+h) t *
    triangleSq (qfactorial q) 0 (m-t) (l-t+h) (c-(m-t))

def typeIRightShiftedTriangleSq (q : ℝ) (h l m c t : ℕ) : ℝ :=
  triangleSq (qfactorial q) 0 (c-(m-t)) (t+h) (m-t) *
    triangleSq (qfactorial q) 0 t (c-(m-t)+h) (l-t)

def typeILeftDimension (q : ℝ) (h l m t : ℕ) : ℝ :=
  mixedWeyl (qfactorial q) (qnum q) h (l-t) (m-t)

def typeIRightDimension (q : ℝ) (h m c t : ℕ) : ℝ :=
  mixedWeyl (qfactorial q) (qnum q) h (c-(m-t)) t

def typeIAMSPrefactor (q : ℝ) (h l m c s t : ℕ) : ℝ :=
  factorialConstant (qfactorial q) h *
    Real.sqrt (typeILeftTriangleSq q h l m c s*typeIRightTriangleSq q h l m c t)

theorem quantumTriangleSq_pos (q : ℝ) (hq : 0<q) (h p r u : ℕ) :
    0<triangleSq (qfactorial q) h p r u :=
  div_pos (mul_pos (mul_pos (qfactorial_pos q hq _) (qfactorial_pos q hq _)) (qfactorial_pos q hq _))
    (qfactorial_pos q hq _)

theorem factorialConstant_quantum_pos (q : ℝ) (hq : 0<q) (h : ℕ) :
    0<factorialConstant (qfactorial q) h := mul_pos (qfactorial_pos q hq _) (qfactorial_pos q hq _)

theorem mixedWeyl_actual_dimension (q : ℝ) (hq : 0<q) (hq1 : q≠1) (h p r : ℕ) :
    mixedWeyl (qfactorial q) (qnum q) h p r=
      mixedIrrepQuantumDimension q hq hq1 (h+1) (by omega) p r := by
  rw [mixedIrrepQuantumDimension_closed]
  have hp : p+(h+1)-1=p+h := by omega
  have hr : r+(h+1)-1=r+h := by omega
  rw [hp,hr,show h+1-1=h from by omega]
  unfold mixedWeyl factorialConstant
  simp only [Nat.add_assoc]
  ring

theorem mixedWeyl_quantum_pos (q : ℝ) (hq : 0<q) (h p r : ℕ) :
    0<mixedWeyl (qfactorial q) (qnum q) h p r := by
  unfold mixedWeyl
  exact div_pos (mul_pos (mul_pos (qnum_pos q hq _ (by omega)) (qfactorial_pos q hq _)) (qfactorial_pos q hq _))
    (mul_pos (mul_pos (qfactorial_pos q hq _) (qfactorial_pos q hq _)) (factorialConstant_quantum_pos q hq _))

theorem typeILeftNormalization (q : ℝ) (hq : 0<q) (h l m c t : ℕ) :
    typeILeftDimension q h l m t*factorialConstant (qfactorial q) h*typeILeftTriangleSq q h l m c t/
      typeILeftShiftedTriangleSq q h l m c t=qnum q ((l-t)+(m-t)+h+1) := by
  simpa only [typeILeftDimension,typeILeftTriangleSq,typeILeftShiftedTriangleSq,mul_assoc] using
    quantum_mixed_normalization q hq h (l-t) (m-t) t (c-(m-t))

theorem typeIRightNormalization (q : ℝ) (hq : 0<q) (h l m c t : ℕ) :
    typeIRightDimension q h m c t*factorialConstant (qfactorial q) h*typeIRightTriangleSq q h l m c t/
      typeIRightShiftedTriangleSq q h l m c t=qnum q ((c-(m-t))+t+h+1) := by
  simpa only [typeIRightDimension,typeIRightTriangleSq,typeIRightShiftedTriangleSq,mul_assoc] using
    quantum_mixed_normalization q hq h (c-(m-t)) t (m-t) (l-t)

theorem typeILeftTriangleSq_pos (q : ℝ) (hq : 0<q) (h l m c t : ℕ) :
    0<typeILeftTriangleSq q h l m c t :=
  mul_pos (quantumTriangleSq_pos q hq _ _ _ _) (quantumTriangleSq_pos q hq _ _ _ _)

theorem typeIRightTriangleSq_pos (q : ℝ) (hq : 0<q) (h l m c t : ℕ) :
    0<typeIRightTriangleSq q h l m c t :=
  mul_pos (quantumTriangleSq_pos q hq _ _ _ _) (quantumTriangleSq_pos q hq _ _ _ _)

theorem typeILeftShiftedTriangleSq_pos (q : ℝ) (hq : 0<q) (h l m c t : ℕ) :
    0<typeILeftShiftedTriangleSq q h l m c t :=
  mul_pos (quantumTriangleSq_pos q hq _ _ _ _) (quantumTriangleSq_pos q hq _ _ _ _)

theorem typeIRightShiftedTriangleSq_pos (q : ℝ) (hq : 0<q) (h l m c t : ℕ) :
    0<typeIRightShiftedTriangleSq q h l m c t :=
  mul_pos (quantumTriangleSq_pos q hq _ _ _ _) (quantumTriangleSq_pos q hq _ _ _ _)

theorem typeIAMSPrefactor_pos (q : ℝ) (hq : 0<q) (h l m c s t : ℕ) :
    0<typeIAMSPrefactor q h l m c s t :=
  mul_pos (factorialConstant_quantum_pos q hq _) (Real.sqrt_pos.mpr
    (mul_pos (typeILeftTriangleSq_pos q hq _ _ _ _ _) (typeIRightTriangleSq_pos q hq _ _ _ _ _)))

end AMSPhysical
#print axioms AMSPhysical.mixedWeyl_actual_dimension
#print axioms AMSPhysical.typeILeftNormalization

