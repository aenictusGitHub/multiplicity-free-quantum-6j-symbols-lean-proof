import StandardCupFirstBoundarySigns

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

theorem standardClebschCoefficient_highest_first (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (l m : ℕ) (r : Fin (min l m+1)) :
    standardClebschCoefficient q hq hq1 l m r 0 0 r.val =
      (Real.sqrt (quantumHighestNorm q l m r))⁻¹ := by
  rw [standardClebschCoefficient_first_zero,if_pos (by simp),
    ← quantumHighestNorm_closed q hq hq1 l m r]
  simp [qFalling]

theorem quantumLeftTreeHighest_highest_first (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (l m c : ℕ) (p : LeftHighestPath l m c) (hp : p.1.val=0) :
    (((standardWeightBasis (K:=ℝ) l).tensorProduct (standardWeightBasis (K:=ℝ) m)).tensorProduct
      (standardWeightBasis (K:=ℝ) c)).repr
      (quantumLeftTreeHighest q hq hq1 l m c p.1 p.2) ((0,0),⟨p.2.val,by
        have hh:=channel_right_bound (coupledLabel l m p.1) c p.2;omega⟩) =
      (Real.sqrt (quantumHighestNorm q (coupledLabel l m p.1) c p.2))⁻¹ *
        (Real.sqrt (quantumHighestNorm q l m p.1))⁻¹ := by
  rw [quantumLeftTreeHighest_basis_coefficient]
  rw [Finset.sum_eq_single 0]
  · have ha : (leftRootIndexPair l m c p 0).1=0 := by
      apply Fin.ext
      simp [leftRootIndexPair,couplingBasisIndex]
    have hb : (leftRootIndexPair l m c p 0).2=⟨p.2.val,by
        have hh:=channel_right_bound (coupledLabel l m p.1) c p.2;omega⟩ := by
      apply Fin.ext
      simp [leftRootIndexPair,couplingBasisIndex]
    rw [ha,hb,if_pos rfl]
    have hc : standardClebschCoefficient q hq hq1 l m p.1 0 0 0 =
        (Real.sqrt (quantumHighestNorm q l m p.1))⁻¹ := by
      simpa only [hp,Nat.cast_zero] using standardClebschCoefficient_highest_first q hq hq1 l m p.1
    simp only [Fin.val_zero,Nat.cast_zero]
    rw [hc]
    simp [couplingCoefficient]
  · intro t ht ht0
    have hm : (0:ℤ)+0≠(p.1.val:ℤ)+((leftRootIndexPair l m c p t).1.val:ℤ) := by
      have htv : t.val≠0 := by intro he;exact ht0 (Fin.ext he)
      simp only [leftRootIndexPair,couplingBasisIndex,Fin.val_mk,hp]
      omega
    simp only [Fin.val_zero,Nat.cast_zero]
    rw [standardClebschCoefficient_weight_mismatch q hq hq1 l m p.1 _ 0 0 hm,mul_zero,zero_mul]
  · simp

theorem standardCupLeftHighest_zero_highest_first_pos (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (l m b c : ℕ) (hm : m≤c) :
    0 < (((standardWeightBasis (K:=ℝ) l).tensorProduct (standardWeightBasis (K:=ℝ) (m+b))).tensorProduct
      (standardWeightBasis (K:=ℝ) c)).repr
      (standardCupLeftHighest q hq hq1 l m b c (by omega)
        ⟨⟨0,by omega⟩,by constructor <;> simp_all⟩).val ((0,0),⟨m,by omega⟩) := by
  change 0 < (((standardWeightBasis (K:=ℝ) l).tensorProduct (standardWeightBasis (K:=ℝ) (m+b))).tensorProduct
    (standardWeightBasis (K:=ℝ) c)).repr
    (quantumLeftTreeHighest q hq hq1 l (m+b) c
      (quantumCupLeftPath l m b c ⟨⟨0,by omega⟩,by constructor <;> simp_all⟩).1
      (quantumCupLeftPath l m b c ⟨⟨0,by omega⟩,by constructor <;> simp_all⟩).2) _
  have he:=quantumLeftTreeHighest_highest_first q hq hq1 l (m+b) c
    (quantumCupLeftPath l m b c ⟨⟨0,by omega⟩,by constructor <;> simp_all⟩) rfl
  simp only [quantumCupLeftPath,Nat.sub_zero] at he ⊢
  rw [he]
  exact mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr (quantumHighestNorm_pos q hq _ _ _)))
    (inv_pos.mpr (Real.sqrt_pos.mpr (quantumHighestNorm_pos q hq _ _ _)))

end AMSPhysical
#print axioms AMSPhysical.standardCupLeftHighest_zero_highest_first_pos
