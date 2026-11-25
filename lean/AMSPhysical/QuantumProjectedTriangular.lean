import QuantumProjectedCoordinates
import TriangularCoordinates

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical
open Module

/-- The projected left highest vectors are triangular in the middle weight. -/
theorem quantumLeftTreeHighest_projected_below (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ)
    (p : LeftHighestPath l m n) (y z : ℤ) (hy : y<(p.1.val:ℤ)) :
    finiteTensorCoefficient m n y z (firstTripleProjection l m n
      (quantumLeftTreeHighest q hq hq1 l m n p.1 p.2))=0 := by
  rw [quantumLeftTreeHighest_coefficient]
  have hz : (∑ k : Fin (p.2.val+1),couplingCoefficient q (n:ℤ) p.2.val k.val*
      standardClebschCoefficient q hq hq1 l m p.1 (leftRootIndexPair l m n p k).1 0 y*
      (if (((leftRootIndexPair l m n p k).2.val):ℤ)=z then 1 else 0))=0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [standardClebschCoefficient_weight_mismatch q hq hq1 l m p.1
      (leftRootIndexPair l m n p k).1 0 y (by change (0:ℤ)+y≠(p.1.val:ℤ)+(k.val:ℤ);omega),mul_zero,zero_mul]
  rw [hz,mul_zero]

theorem standardClebschCoefficient_highest_leading (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ)
    (r : Fin (min l m+1)) : standardClebschCoefficient q hq hq1 l m r 0 0 r.val=
      (Real.sqrt (quantumHighestNorm q l m r))⁻¹ := by
  unfold standardClebschCoefficient unitaryQuantumClebschMap
  rw [LinearMap.smul_apply,quantumClebschMap_highest,map_smul,map_smul,
    finiteCoupledHighest_forget,coupledHighest_coefficient,smul_eq_mul,mul_one]

/-- Its diagonal coefficient is strictly positive in the fixed coupling gauge. -/
theorem quantumLeftTreeHighest_projected_leading (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ)
    (p : LeftHighestPath l m n) :
    finiteTensorCoefficient m n p.1.val p.2.val (firstTripleProjection l m n
      (quantumLeftTreeHighest q hq hq1 l m n p.1 p.2))=
      (Real.sqrt (quantumHighestNorm q (coupledLabel l m p.1) n p.2))⁻¹*
        (Real.sqrt (quantumHighestNorm q l m p.1))⁻¹ := by
  classical
  rw [quantumLeftTreeHighest_coefficient]
  congr 1
  rw [Finset.sum_eq_single 0]
  · have h0 : (leftRootIndexPair l m n p 0).1=0 := by apply Fin.ext;rfl
    have hs : ((leftRootIndexPair l m n p 0).2.val:ℤ)=(p.2.val:ℤ) := by
      change ((p.2.val-0:ℕ):ℤ)=(p.2.val:ℤ)
      omega
    rw [h0,if_pos hs,standardClebschCoefficient_highest_leading]
    simp only [couplingCoefficient,Fin.val_zero,qFalling,pow_zero,one_mul,mul_one,zpow_zero,
      one_div,inv_one,mul_zero,sub_zero,neg_zero,Nat.cast_zero]
  · intro k hk hk0
    have hne : (0:ℤ)+(p.1.val:ℤ)≠(p.1.val:ℤ)+((leftRootIndexPair l m n p k).1.val:ℤ) := by
      change (0:ℤ)+(p.1.val:ℤ)≠(p.1.val:ℤ)+(k.val:ℤ)
      have hkval : k.val≠0 := fun he => hk0 (Fin.ext he)
      omega
    rw [standardClebschCoefficient_weight_mismatch q hq hq1 l m p.1
      (leftRootIndexPair l m n p k).1 0 p.1.val hne,mul_zero,zero_mul]
  · simp

theorem quantumLeftTreeHighest_projected_leading_pos (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ)
    (p : LeftHighestPath l m n) :
    0<finiteTensorCoefficient m n p.1.val p.2.val (firstTripleProjection l m n
      (quantumLeftTreeHighest q hq hq1 l m n p.1 p.2)) := by
  rw [quantumLeftTreeHighest_projected_leading]
  exact mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr (quantumHighestNorm_pos q hq _ _ _)))
    (inv_pos.mpr (Real.sqrt_pos.mpr (quantumHighestNorm_pos q hq _ _ _)))

end AMSPhysical

#print axioms AMSPhysical.quantumLeftTreeHighest_projected_leading_pos
