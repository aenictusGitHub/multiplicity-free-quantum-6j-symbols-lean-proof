import QuantumTypeIIRightChannels

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical

/-- Physical Type-II right coupling vector in its independently identified
mixed irreducible channel, pulled through an actual module isometry. -/
def physicalTypeIIRightCoupling (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c d : ℕ) (hbal : a+b=c+d) (t : QuantumCupIndex a c b) :
    physicalTypeIIHighestSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c d :=
  (physicalTypeIIToCompleteI q hq hq1 n hn a b c d hbal).symm
    (physicalTypeIRightCoupling q hq hq1 n hn a c 0 b (by omega) (Or.inl rfl) t)

theorem physicalTypeIIRightCoupling_pair (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c d : ℕ) (hbal : a+b=c+d) (s t : QuantumCupIndex a c b) :
    physicalTypeIITripleBilin q n a b c
      (physicalTypeIIRightCoupling q hq hq1 n hn a b c d hbal s).val
      (physicalTypeIIRightCoupling q hq hq1 n hn a b c d hbal t).val=if s=t then 1 else 0 := by
  have he:=physicalTypeIIToCompleteI_isometry q hq hq1 n hn a b c d hbal
    (physicalTypeIIRightCoupling q hq hq1 n hn a b c d hbal s)
    (physicalTypeIIRightCoupling q hq hq1 n hn a b c d hbal t)
  simp only [physicalTypeIIRightCoupling,LinearEquiv.apply_symm_apply,physicalTypeIRightCoupling_pair] at he
  exact he.symm.trans (physicalTypeIRightCoupling_pair q hq hq1 n hn a c 0 b (by omega) (Or.inl rfl) s t)

theorem physicalTypeIIRightCoupling_mem (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c d : ℕ) (hbal : a+b=c+d) (t : QuantumCupIndex a c b) :
    (physicalTypeIIRightCoupling q hq hq1 n hn a b c d hbal t).val∈
      physicalTypeIIRightChannel q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c t := by
  apply (physicalTypeIIToCompleteI_right_mem_iff q hq hq1 n hn a b c d hbal t _).mp
  unfold physicalTypeIIRightCoupling
  rw [LinearEquiv.apply_symm_apply]
  exact physicalTypeIRightCoupling_mem_channel q hq hq1 n hn a c 0 b (by omega) (Or.inl rfl) t

/-- COMPLETE actual physical Type-II right coupling basis. -/
def physicalTypeIIRightBasis (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c d : ℕ) (hbal : a+b=c+d) :
    Module.Basis (QuantumCupIndex a c b) ℝ
      (physicalTypeIIHighestSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c d) :=
  (physicalTypeIRightBasis q hq hq1 n hn a c 0 b (by omega) (Or.inl rfl)).map
    (physicalTypeIIToCompleteI q hq hq1 n hn a b c d hbal).symm

theorem physicalTypeIIRightBasis_apply (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c d : ℕ) (hbal : a+b=c+d) (t : QuantumCupIndex a c b) :
    physicalTypeIIRightBasis q hq hq1 n hn a b c d hbal t=
      physicalTypeIIRightCoupling q hq hq1 n hn a b c d hbal t := by
  rw [physicalTypeIIRightBasis,Module.Basis.map_apply,physicalTypeIRightBasis_apply]
  rfl

end AMSPhysical
#print axioms AMSPhysical.physicalTypeIIRightBasis
#print axioms AMSPhysical.physicalTypeIIRightCoupling_mem
