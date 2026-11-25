import QuantumPhysicalCupTransport
import QuantumPhysicalTripleMetric
import QuantumFiniteTripleRadial

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical

theorem occupationTripleCoefficients_cupSpan_synthesis (q : ℝ) (hq : 0<q) (n : ℕ) (hn : 0<n)
    (l m h c : ℕ) (v : quantumCupSpan q n l m h c) :
    occupationTripleCoefficients n l (m+h) c (occupationTripleSynthesis n l (m+h) c v.val)=v.val := by
  have h0:=physicalQuantumCupCoefficientEquiv_literal q hq n hn l m h c
    ((physicalQuantumCupCoefficientEquiv q hq n hn l m h c).symm v)
  rw [LinearEquiv.apply_symm_apply,physicalQuantumCupCoefficientEquiv_inverse_literal] at h0
  exact h0.symm

def quantumCupPhysicalBilin (q : ℝ) (n l m h c : ℕ) :
    quantumCupSpan q n l m h c →ₗ[ℝ] quantumCupSpan q n l m h c →ₗ[ℝ] ℝ := by
  let V := quantumCupSpan q n l m h c
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  let T : V →ₗ[ℝ] quantumOccupationTripleSpace n l (m+h) c :=
    (occupationTripleSynthesis n l (m+h) c).comp (quantumCupSpan q n l m h c).subtype
  exact ((physicalTripleBilin q n l (m+h) c).comp T).compl₂ T

theorem quantumCupPhysicalBilin_symm (q : ℝ) (n l m h c : ℕ) (v w : quantumCupSpan q n l m h c) :
    quantumCupPhysicalBilin q n l m h c v w=quantumCupPhysicalBilin q n l m h c w v :=
  physicalTripleBilin_symm q n l (m+h) c _ _

theorem quantumCupPhysicalBilin_definite (q : ℝ) (hq : 0<q) (n : ℕ) (hn : 0<n)
    (l m h c : ℕ) (v : quantumCupSpan q n l m h c) (hv : quantumCupPhysicalBilin q n l m h c v v=0) : v=0 := by
  have hs:=physicalTripleBilin_definite q hq n l (m+h) c (occupationTripleSynthesis n l (m+h) c v.val) hv
  have hc0:=occupationTripleCoefficients_cupSpan_synthesis q hq n hn l m h c v
  rw [hs,map_zero] at hc0
  exact Subtype.ext hc0.symm

theorem quantumCupPhysicalBilin_nonneg (q : ℝ) (hq : 0<q) (n l m h c : ℕ) (v : quantumCupSpan q n l m h c) :
    0 ≤ quantumCupPhysicalBilin q n l m h c v v := physicalTripleBilin_nonneg q hq n l (m+h) c _

theorem quantumCupPhysicalBilin_pos (q : ℝ) (hq : 0<q) (n : ℕ) (hn : 0<n)
    (l m h c : ℕ) (v : quantumCupSpan q n l m h c) (hv : v≠0) :
    0<quantumCupPhysicalBilin q n l m h c v v := by
  have hnonneg:=quantumCupPhysicalBilin_nonneg q hq n l m h c v
  have hne : quantumCupPhysicalBilin q n l m h c v v≠0 := fun he =>hv (quantumCupPhysicalBilin_definite q hq n hn l m h c v he)
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

theorem quantumCupLeftAction_physical_synthesis (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b m h c : ℕ) (hb : m+h=b+1) (v : quantumCupSpan q n (a+1) m h c) :
    occupationTripleSynthesis n (a+1) (b+1) c
        (quantumCupLeftAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn (a+1) m h c v).val=
      finiteTripleLeftRadial q n a b c (occupationTripleSynthesis n (a+1) (b+1) c v.val) := by
  have hSynth (w : quantumCupSpan q n (a+1) m h c) :
      occupationTripleCoefficients n (a+1) (b+1) c (occupationTripleSynthesis n (a+1) (b+1) c w.val)=w.val := by
    rw [← hb]
    exact occupationTripleCoefficients_cupSpan_synthesis q hq n hn (a+1) m h c w
  apply occupationTripleCoefficients_injective n (a+1) (b+1) c
  rw [hSynth,occupationTripleCoefficients_leftRadial,hSynth]
  rfl

theorem quantumCupRightAction_physical_synthesis (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l a b m h : ℕ) (ha : m+h=a+1) (v : quantumCupSpan q n l m h (b+1)) :
    occupationTripleSynthesis n l (a+1) (b+1)
        (quantumCupRightAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m h (b+1) v).val=
      finiteTripleRightRadial q n l a b (occupationTripleSynthesis n l (a+1) (b+1) v.val) := by
  have hSynth (w : quantumCupSpan q n l m h (b+1)) :
      occupationTripleCoefficients n l (a+1) (b+1) (occupationTripleSynthesis n l (a+1) (b+1) w.val)=w.val := by
    rw [← ha]
    exact occupationTripleCoefficients_cupSpan_synthesis q hq n hn l m h (b+1) w
  apply occupationTripleCoefficients_injective n l (a+1) (b+1)
  rw [hSynth,occupationTripleCoefficients_rightRadial,hSynth]
  rfl

theorem quantumCupLeftAction_physical_selfAdjoint_positive (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b m h c : ℕ) (hb : m+h=b+1) :
    PairAdjoint (V:=quantumCupSpan q n (a+1) m h c) (quantumCupPhysicalBilin q n (a+1) m h c)
      (quantumCupLeftAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn (a+1) m h c)
      (quantumCupLeftAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn (a+1) m h c) := by
  intro u v
  change physicalTripleBilin q n (a+1) (m+h) c
      (occupationTripleSynthesis n (a+1) (m+h) c (quantumCupLeftAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn (a+1) m h c u).val) (occupationTripleSynthesis n (a+1) (m+h) c v.val)=
    physicalTripleBilin q n (a+1) (m+h) c (occupationTripleSynthesis n (a+1) (m+h) c u.val)
      (occupationTripleSynthesis n (a+1) (m+h) c (quantumCupLeftAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn (a+1) m h c v).val)
  rw [hb,quantumCupLeftAction_physical_synthesis q hq hq1 n hn a b m h c hb,
    quantumCupLeftAction_physical_synthesis q hq hq1 n hn a b m h c hb]
  exact finiteTripleLeftRadial_selfAdjoint q hq hq1 n a b c _ _

theorem quantumCupRightAction_physical_selfAdjoint_positive (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l a b m h : ℕ) (ha : m+h=a+1) :
    PairAdjoint (V:=quantumCupSpan q n l m h (b+1)) (quantumCupPhysicalBilin q n l m h (b+1))
      (quantumCupRightAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m h (b+1))
      (quantumCupRightAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m h (b+1)) := by
  intro u v
  change physicalTripleBilin q n l (m+h) (b+1)
      (occupationTripleSynthesis n l (m+h) (b+1) (quantumCupRightAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m h (b+1) u).val) (occupationTripleSynthesis n l (m+h) (b+1) v.val)=
    physicalTripleBilin q n l (m+h) (b+1) (occupationTripleSynthesis n l (m+h) (b+1) u.val)
      (occupationTripleSynthesis n l (m+h) (b+1) (quantumCupRightAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m h (b+1) v).val)
  rw [ha,quantumCupRightAction_physical_synthesis q hq hq1 n hn l a b m h ha,
    quantumCupRightAction_physical_synthesis q hq hq1 n hn l a b m h ha]
  exact finiteTripleRightRadial_selfAdjoint q hq hq1 n l a b _ _

end AMSPhysical
