import QuantumJacobiStep

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
open Module

def projectedLeftNextRatio (q : ℝ) (l m n : ℕ) (p : LeftHighestPath l m n) : ℝ :=
  couplingCoefficient q (n:ℤ) p.2.val 1*(qInteger q (coupledLabel l m p.1:ℤ))⁻¹*
    q^(-(l:ℤ))*qInteger q ((m:ℤ)-(p.1.val:ℤ))

theorem couplingCoefficient_one (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℤ) (s : ℕ) :
    couplingCoefficient q n s 1= -qInteger q (s:ℤ)/q^(n-2*((s:ℤ)-1)) := by
  simp only [couplingCoefficient,Nat.zero_add,Nat.cast_zero,Nat.cast_one,sub_zero,one_mul,
    qInteger_one q (qInteger_denominator_ne_zero q hq hq1)]

theorem projectedLeftNextRatio_zero (q : ℝ) (l m n : ℕ) (p : LeftHighestPath l m n)
    (hs : p.2.val=0) : projectedLeftNextRatio q l m n p=0 := by
  unfold projectedLeftNextRatio
  rw [hs]
  simp only [couplingCoefficient,Nat.cast_zero,sub_zero,qInteger_zero,mul_zero,neg_zero,
    zero_div,zero_mul]

/-- The second projected coordinate follows from the actual one-step Clebsch coefficient. -/
theorem quantumLeftTreeHighest_projected_next (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ)
    (p : LeftHighestPath l m n) :
    finiteTensorCoefficient m n ((p.1.val:ℤ)+1) ((p.2.val:ℤ)-1) (firstTripleProjection l m n
      (quantumLeftTreeHighest q hq hq1 l m n p.1 p.2))=
      projectedLeftLeading q l m n p*projectedLeftNextRatio q l m n p := by
  classical
  rw [quantumLeftTreeHighest_coefficient]
  by_cases hs : p.2.val=0
  · rw [projectedLeftNextRatio_zero q l m n p hs,mul_zero]
    have hz : (∑ k : Fin (p.2.val+1),couplingCoefficient q (n:ℤ) p.2.val k.val*
        standardClebschCoefficient q hq hq1 l m p.1 (leftRootIndexPair l m n p k).1 0 ((p.1.val:ℤ)+1)*
        (if (((leftRootIndexPair l m n p k).2.val):ℤ)=(p.2.val:ℤ)-1 then 1 else 0))=0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have hk0 : k.val=0 := by have hh := k.isLt;omega
      rw [standardClebschCoefficient_weight_mismatch q hq hq1 l m p.1
        (leftRootIndexPair l m n p k).1 0 ((p.1.val:ℤ)+1)
        (by change (0:ℤ)+((p.1.val:ℤ)+1)≠(p.1.val:ℤ)+(k.val:ℤ);omega),mul_zero,zero_mul]
    rw [hz,mul_zero]
  · let k1 : Fin (p.2.val+1) := ⟨1,by omega⟩
    have hsum : (∑ k : Fin (p.2.val+1),couplingCoefficient q (n:ℤ) p.2.val k.val*
        standardClebschCoefficient q hq hq1 l m p.1 (leftRootIndexPair l m n p k).1 0 ((p.1.val:ℤ)+1)*
        (if (((leftRootIndexPair l m n p k).2.val):ℤ)=(p.2.val:ℤ)-1 then 1 else 0))=
        couplingCoefficient q (n:ℤ) p.2.val 1*
          standardClebschCoefficient q hq hq1 l m p.1 (leftRootIndexPair l m n p k1).1 0 ((p.1.val:ℤ)+1) := by
      rw [Finset.sum_eq_single k1]
      · have hi : (((leftRootIndexPair l m n p k1).2.val):ℤ)=(p.2.val:ℤ)-1 := by
          change ((p.2.val-1:ℕ):ℤ)=(p.2.val:ℤ)-1
          omega
        rw [if_pos hi,mul_one]
      · intro k hk hk1
        have hkv : k.val≠1 := fun he => hk1 (Fin.ext he)
        rw [standardClebschCoefficient_weight_mismatch q hq hq1 l m p.1
          (leftRootIndexPair l m n p k).1 0 ((p.1.val:ℤ)+1)
          (by change (0:ℤ)+((p.1.val:ℤ)+1)≠(p.1.val:ℤ)+(k.val:ℤ);omega),mul_zero,zero_mul]
      · simp
    rw [hsum,standardClebschCoefficient_first_zero]
    have hi : ((leftRootIndexPair l m n p k1).1.val)=1 := rfl
    rw [if_pos (by rw [hi];norm_num)]
    rw [hi,← quantumHighestNorm_closed q hq hq1 l m p.1]
    simp only [qFalling,Nat.cast_zero,Nat.cast_one,sub_zero,mul_one,one_mul,neg_mul,
      Int.cast_one]
    unfold projectedLeftLeading projectedLeftNextRatio
    ring

/-- Fully explicit phase and quantum-number expression for the next-coordinate ratio. -/
theorem projectedLeftNextRatio_closed (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ)
    (p : LeftHighestPath l m n) :
    projectedLeftNextRatio q l m n p=
      -q^(-(l:ℤ)-(n:ℤ)+2*(p.2.val:ℤ)-2)*qInteger q (p.2.val:ℤ)*
        qInteger q ((m:ℤ)-(p.1.val:ℤ))/qInteger q (coupledLabel l m p.1:ℤ) := by
  unfold projectedLeftNextRatio
  rw [couplingCoefficient_one q hq hq1]
  have hp : (q^((n:ℤ)-2*((p.2.val:ℤ)-1)))⁻¹*q^(-(l:ℤ))=
      q^(-(l:ℤ)-(n:ℤ)+2*(p.2.val:ℤ)-2) := by
    rw [← zpow_neg,← zpow_add₀ (ne_of_gt hq)]
    congr 1
    omega
  simp only [div_eq_mul_inv]
  linear_combination -(qInteger q (p.2.val:ℤ))*
    (qInteger q (coupledLabel l m p.1:ℤ))⁻¹*qInteger q ((m:ℤ)-(p.1.val:ℤ))*hp

end AMSPhysical

#print axioms AMSPhysical.quantumLeftTreeHighest_projected_next
#print axioms AMSPhysical.projectedLeftNextRatio_closed
