import QuantumCupPhysicalMetric

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical

theorem quantumCupLeftAction_zero_first (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n) (m h c : ℕ) :
    quantumCupLeftAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn 0 m h c=0 := by
  apply (quantumCupBasis q hq n hn 0 m h c).ext
  intro r
  have hr : r.val.val=0 := by have hh:=r.property.1;omega
  rw [quantumCupBasis_apply,quantumCupLeftAction_vector]
  split_ifs <;> simp [quantumCupLeftDiagonal,quantumCupLeftOffDiagonal,hr]

theorem quantumCupLeftAction_zero_middle (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l m h c : ℕ) (hm : m+h=0) :
    quantumCupLeftAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m h c=0 := by
  have hm0 : m=0 := by omega
  have hh0 : h=0 := by omega
  subst m
  subst h
  apply (quantumCupBasis q hq n hn l 0 0 c).ext
  intro r
  have hr : r.val.val=0 := by have hh:=r.val.isLt;omega
  rw [quantumCupBasis_apply,quantumCupLeftAction_vector]
  split_ifs <;> simp [quantumCupLeftDiagonal,quantumCupLeftOffDiagonal,hr]

theorem quantumCupRightAction_zero_third (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n) (l m h : ℕ) :
    quantumCupRightAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m h 0=0 := by
  apply (quantumCupBasis q hq n hn l m h 0).ext
  intro r
  have hr : m-r.val.val=0 := by have hh:=r.property.2;omega
  rw [quantumCupBasis_apply,quantumCupRightAction_vector]
  split_ifs <;> simp [quantumCupLeftDiagonal,quantumCupLeftOffDiagonal,hr]

theorem quantumCupRightAction_zero_middle (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l m h c : ℕ) (hm : m+h=0) :
    quantumCupRightAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m h c=0 := by
  have hm0 : m=0 := by omega
  have hh0 : h=0 := by omega
  subst m
  subst h
  apply (quantumCupBasis q hq n hn l 0 0 c).ext
  intro r
  have hr : r.val.val=0 := by have hh:=r.val.isLt;omega
  rw [quantumCupBasis_apply,quantumCupRightAction_vector]
  split_ifs <;> simp [quantumCupLeftDiagonal,quantumCupLeftOffDiagonal,hr]

/-- Both actual radial operators are self-adjoint for the literal physical
compact metric, including every zero-degree boundary. -/
theorem quantumCupLeftAction_physical_selfAdjoint (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l m h c : ℕ) : PairAdjoint (V:=quantumCupSpan q n l m h c) (quantumCupPhysicalBilin q n l m h c)
      (quantumCupLeftAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m h c)
      (quantumCupLeftAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m h c) := by
  by_cases hl : l=0
  · subst l
    rw [quantumCupLeftAction_zero_first q hq hq1]
    intro u v
    simp
  · by_cases hm : m+h=0
    · rw [quantumCupLeftAction_zero_middle q hq hq1 n hn l m h c hm]
      intro u v
      simp
    · obtain ⟨a,rfl⟩:=Nat.exists_eq_succ_of_ne_zero hl
      exact quantumCupLeftAction_physical_selfAdjoint_positive q hq hq1 n hn a (m+h-1) m h c (by omega)

theorem quantumCupRightAction_physical_selfAdjoint (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l m h c : ℕ) : PairAdjoint (V:=quantumCupSpan q n l m h c) (quantumCupPhysicalBilin q n l m h c)
      (quantumCupRightAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m h c)
      (quantumCupRightAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m h c) := by
  by_cases hc : c=0
  · subst c
    rw [quantumCupRightAction_zero_third q hq hq1]
    intro u v
    simp
  · by_cases hm : m+h=0
    · rw [quantumCupRightAction_zero_middle q hq hq1 n hn l m h c hm]
      intro u v
      simp
    · obtain ⟨b,rfl⟩:=Nat.exists_eq_succ_of_ne_zero hc
      exact quantumCupRightAction_physical_selfAdjoint_positive q hq hq1 n hn l (m+h-1) b m h (by omega)

end AMSPhysical
#print axioms AMSPhysical.quantumCupLeftAction_physical_selfAdjoint
#print axioms AMSPhysical.quantumCupRightAction_physical_selfAdjoint
