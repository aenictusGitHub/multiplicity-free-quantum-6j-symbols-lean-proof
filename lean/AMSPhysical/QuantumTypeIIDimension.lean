import QuantumTypeIICommonIndex
import QuantumTypeIITriple
import QuantumCupHighestComplete

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical

theorem physicalTypeIIHighest_finrank (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c d : ℕ) (hbal : a+b=c+d) :
    Module.finrank ℝ (physicalTypeIIHighestSpace q (ne_of_gt hq)
      (qInteger_denominator_ne_zero q hq hq1) n a b c d)=Fintype.card (TypeIICommonIndex a b c d) := by
  have hd : a+b-c=d := by omega
  have he:=physicalQuantumCupSpan_eq_highest q hq hq1 n hn a c 0 b (by omega) (Or.inl rfl)
  simp only [Nat.add_zero,hd] at he
  calc
    _ = Module.finrank ℝ (typeAHighestSpace q n
      (typeAMixedTriple q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a c b)
      (mixedHighestDynkin n d 0)) := (physicalTypeIIHighestToI q hq hq1 n hn a b c d).finrank_eq
    _ = Fintype.card (QuantumCupIndex a c b) := by
      rw [← he]
      exact Module.finrank_eq_card_basis (physicalQuantumCupBasis q hq n hn a c 0 b)
    _ = Fintype.card (TypeIICommonIndex a b c d) := (Fintype.card_congr (typeIICommonCupEquiv a b c d hbal)).symm

end AMSPhysical
#print axioms AMSPhysical.physicalTypeIIHighest_finrank
