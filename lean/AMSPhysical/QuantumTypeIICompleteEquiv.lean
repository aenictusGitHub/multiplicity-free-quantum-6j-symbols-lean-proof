import QuantumTypeIITriple
import PhysicalTypeICouplingBases

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical

def physicalTypeIIToCompleteI (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c d : ℕ) (hbal : a+b=c+d) :
    physicalTypeIIHighestSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c d ≃ₗ[ℝ]
    physicalQuantumHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a c 0 b :=
  (physicalTypeIIHighestToI q hq hq1 n hn a b c d).trans
    (LinearEquiv.ofEq _ _ (by
      have hd : a+b-c+0=d := by omega
      simp only [physicalQuantumHighestMultiplicity,Nat.add_zero,hd]))

theorem physicalTypeIIToCompleteI_val (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c d : ℕ) (hbal : a+b=c+d)
    (v : physicalTypeIIHighestSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c d) :
    (physicalTypeIIToCompleteI q hq hq1 n hn a b c d hbal v).val=
      physicalTypeIIToI q hq hq1 n hn a b c v.val := by
  unfold physicalTypeIIToCompleteI
  simp only [LinearEquiv.trans_apply,LinearEquiv.coe_ofEq_apply]
  rfl

theorem physicalTypeIIToCompleteI_isometry (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c d : ℕ) (hbal : a+b=c+d)
    (v w : physicalTypeIIHighestSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c d) :
    physicalTripleBilin q n a c b
      (physicalTypeIIToCompleteI q hq hq1 n hn a b c d hbal v).val
      (physicalTypeIIToCompleteI q hq hq1 n hn a b c d hbal w).val=
      physicalTypeIITripleBilin q n a b c v.val w.val := by
  rw [physicalTypeIIToCompleteI_val,physicalTypeIIToCompleteI_val]
  exact physicalTypeIIToI_isometry q hq hq1 n hn a b c v.val w.val

end AMSPhysical
#print axioms AMSPhysical.physicalTypeIIToCompleteI_isometry
