import QuantumTwoRowDimensionClosed
import PhysicalTypeINormalization
import QuantumTypeIICommonIndex

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

def typeIILeftTriangleSq (q : ℝ) (h a b c d r : ℕ) : ℝ :=
  triangleSq (qfactorial q) h (a-r) (b-r) r*triangleSq (qfactorial q) h (c-r) (d-r) r

def typeIILeftShiftedTriangleSq (q : ℝ) (h a b c d r : ℕ) : ℝ :=
  triangleSq (qfactorial q) 0 (a-r) (b-r) (r+h)*triangleSq (qfactorial q) 0 (c-r) (d-r) r

def typeIIRightTriangleSq (q : ℝ) (h a b c t : ℕ) : ℝ :=
  triangleSq (qfactorial q) h t (b-(c-t)) (c-t)*triangleSq (qfactorial q) h (b-(c-t)) t (a-t)

def typeIIRightShiftedTriangleSq (q : ℝ) (h a b c t : ℕ) : ℝ :=
  triangleSq (qfactorial q) 0 t (b-(c-t)+h) (c-t)*triangleSq (qfactorial q) 0 (b-(c-t)) (t+h) (a-t)

def typeIILeftDimension (q : ℝ) (h a b r : ℕ) : ℝ :=
  sameWeyl (qfactorial q) (qnum q) h (a-r) (b-r) r

def typeIIRightDimension (q : ℝ) (h b c t : ℕ) : ℝ :=
  mixedWeyl (qfactorial q) (qnum q) h t (b-(c-t))

def typeIIAMSPrefactor (q : ℝ) (h a b c d r t : ℕ) : ℝ :=
  factorialConstant (qfactorial q) h*Real.sqrt (typeIILeftTriangleSq q h a b c d r*typeIIRightTriangleSq q h a b c t)

theorem typeIILeftDimension_actual (q : ℝ) (hq : 0<q) (hq1 : q≠1) (h a b r : ℕ) :
    typeIILeftDimension q h a b r=
      twoRowIrrepQuantumDimension q hq hq1 (h+1) (by omega) ((a-r)+(b-r)) r :=
  sameWeyl_actual_dimension q hq hq1 h (a-r) (b-r) r

theorem mixedIrrepQuantumDimension_swap (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (p r : ℕ) :
    mixedIrrepQuantumDimension q hq hq1 n hn p r=mixedIrrepQuantumDimension q hq hq1 n hn r p := by
  rw [mixedIrrepQuantumDimension_closed,mixedIrrepQuantumDimension_closed]
  rw [Nat.add_comm p r]
  ring

theorem typeIIRightDimension_actual (q : ℝ) (hq : 0<q) (hq1 : q≠1) (h b c t : ℕ) :
    typeIIRightDimension q h b c t=
      mixedIrrepQuantumDimension q hq hq1 (h+1) (by omega) (b-(c-t)) t := by
  unfold typeIIRightDimension
  rw [mixedWeyl_actual_dimension q hq hq1]
  exact mixedIrrepQuantumDimension_swap q hq hq1 (h+1) (by omega) t (b-(c-t))

theorem typeIILeftNormalization (q : ℝ) (hq : 0<q) (h a b c d : ℕ)
    (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d) :
    typeIILeftDimension q h a b r.val*factorialConstant (qfactorial q) h*
      typeIILeftTriangleSq q h a b c d r.val/typeIILeftShiftedTriangleSq q h a b c d r.val=
        qnum q ((a-r.val)+(b-r.val)+1) := by
  have hr:=r.isLt
  simpa only [typeIILeftDimension,typeIILeftTriangleSq,typeIILeftShiftedTriangleSq,mul_assoc] using
    quantum_same_normalization q hq h (a-r.val) (b-r.val) (c-r.val) (d-r.val) r.val (by omega)

theorem typeIIRightNormalization (q : ℝ) (hq : 0<q) (h a b c t : ℕ) :
    typeIIRightDimension q h b c t*factorialConstant (qfactorial q) h*
      typeIIRightTriangleSq q h a b c t/typeIIRightShiftedTriangleSq q h a b c t=
        qnum q (t+(b-(c-t))+h+1) := by
  simpa only [typeIIRightDimension,typeIIRightTriangleSq,typeIIRightShiftedTriangleSq,mul_assoc] using
    quantum_mixed_normalization q hq h t (b-(c-t)) (c-t) (a-t)

theorem sameWeyl_quantum_pos (q : ℝ) (hq : 0<q) (h p r t : ℕ) :
    0<sameWeyl (qfactorial q) (qnum q) h p r t := by
  unfold sameWeyl
  exact div_pos (mul_pos (mul_pos (qnum_pos q hq _ (by omega)) (qfactorial_pos q hq _)) (qfactorial_pos q hq _))
    (mul_pos (mul_pos (qfactorial_pos q hq _) (qfactorial_pos q hq _)) (factorialConstant_quantum_pos q hq _))

end AMSPhysical
#print axioms AMSPhysical.typeIILeftDimension_actual
#print axioms AMSPhysical.typeIILeftNormalization
