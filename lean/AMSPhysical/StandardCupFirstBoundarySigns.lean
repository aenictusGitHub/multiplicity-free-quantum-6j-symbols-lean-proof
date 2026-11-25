import GlobalRightTreeBoundary
import QuantumClebschSecondZero
import StandardCupHighestVectors

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

theorem quantumLeftTreeHighest_last_coordinate (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (l m c : ℕ) (p : LeftHighestPath l m c) (i : Fin (l+1)) (j : Fin (m+1)) :
    (((standardWeightBasis (K:=ℝ) l).tensorProduct (standardWeightBasis (K:=ℝ) m)).tensorProduct
      (standardWeightBasis (K:=ℝ) c)).repr
      (quantumLeftTreeHighest q hq hq1 l m c p.1 p.2) ((i,j),0) =
      (Real.sqrt (quantumHighestNorm q (coupledLabel l m p.1) c p.2))⁻¹ *
        couplingCoefficient q (c:ℤ) p.2.val p.2.val *
          standardClebschCoefficient q hq hq1 l m p.1
            (leftRootIndexPair l m c p (Fin.last p.2.val)).1 i.val j.val := by
  rw [quantumLeftTreeHighest_basis_coefficient]
  rw [Finset.sum_eq_single (Fin.last p.2.val)]
  · simp only [leftRootIndexPair,couplingBasisIndex,Fin.val_last,Nat.sub_self]
    simp only [Fin.mk_zero',if_true,mul_one,mul_assoc]
  · intro t ht htlast
    have he : (leftRootIndexPair l m c p t).2≠0 := by
      intro he
      apply htlast
      apply Fin.ext
      have hv:=congrArg Fin.val he
      have ht':=t.isLt
      simp only [leftRootIndexPair,couplingBasisIndex,Fin.val_mk,Fin.val_zero] at hv
      simp only [Fin.val_last]
      omega
    rw [if_neg he,mul_zero]
  · simp

theorem standardCupRightHighest_first_boundary_signed_pos (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (l m b c : ℕ) (hadm : m≤l+c) (t : QuantumCupIndex l m c) :
    0 < (-1:ℝ)^(m-t.val.val)*
      (((standardWeightBasis (K:=ℝ) l).tensorProduct (standardWeightBasis (K:=ℝ) (m+b))).tensorProduct
        (standardWeightBasis (K:=ℝ) c)).repr
        (standardCupRightHighest q hq hq1 l m b c hadm t).val ((0,⟨m,by omega⟩),0) := by
  change 0 < (-1:ℝ)^(m-t.val.val)*
    (((standardWeightBasis (K:=ℝ) l).tensorProduct (standardWeightBasis (K:=ℝ) (m+b))).tensorProduct
      (standardWeightBasis (K:=ℝ) c)).repr
      (quantumRightTreeHighest q hq hq1 l (m+b) c
        (quantumCupRightPath l m b c t).1 (quantumCupRightPath l m b c t).2) _
  rw [quantumRightTreeHighest_first_coordinate]
  let p:=quantumCupRightPath l m b c t
  have ht:=t.val.isLt
  have he : (m:ℤ)=((p.1.val:ℤ)+((rightRootIndexPair l (m+b) c p 0).2.val:ℤ)) := by
    simp only [p,quantumCupRightPath,rightRootIndexPair,couplingBasisIndex,Fin.val_zero,Nat.sub_zero]
    omega
  have hp : m-t.val.val=p.1.val := rfl
  rw [hp]
  change 0 < (-1:ℝ)^p.1.val*((Real.sqrt (quantumHighestNorm q l (coupledLabel (m+b) c p.1) p.2))⁻¹ *
    standardClebschCoefficient q hq hq1 (m+b) c p.1 (rightRootIndexPair l (m+b) c p 0).2 (m:ℤ) 0)
  rw [he]
  have ha : p.1.val+(rightRootIndexPair l (m+b) c p 0).2.val≤m+b := by
    simp only [p,quantumCupRightPath,rightRootIndexPair,couplingBasisIndex,Fin.val_zero,Nat.sub_zero]
    omega
  have hc:=standardClebschCoefficient_second_zero_signed_pos q hq hq1 (m+b) c p.1
    (rightRootIndexPair l (m+b) c p 0).2 ha
  have hn:=inv_pos.mpr (Real.sqrt_pos.mpr (quantumHighestNorm_pos q hq l (coupledLabel (m+b) c p.1) p.2))
  nlinarith [mul_pos hn hc]

theorem standardCupLeftHighest_first_boundary_signed_pos (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (l m b c : ℕ) (hadm : m≤l+c) (t : QuantumCupIndex l m c) :
    0 < (-1:ℝ)^(m-t.val.val)*
      (((standardWeightBasis (K:=ℝ) l).tensorProduct (standardWeightBasis (K:=ℝ) (m+b))).tensorProduct
        (standardWeightBasis (K:=ℝ) c)).repr
        (standardCupLeftHighest q hq hq1 l m b c hadm t).val ((0,⟨m,by omega⟩),0) := by
  change 0 < (-1:ℝ)^(m-t.val.val)*
    (((standardWeightBasis (K:=ℝ) l).tensorProduct (standardWeightBasis (K:=ℝ) (m+b))).tensorProduct
      (standardWeightBasis (K:=ℝ) c)).repr
      (quantumLeftTreeHighest q hq hq1 l (m+b) c
        (quantumCupLeftPath l m b c t).1 (quantumCupLeftPath l m b c t).2) _
  rw [quantumLeftTreeHighest_last_coordinate]
  let p:=quantumCupLeftPath l m b c t
  have hr : p.2.val=m-t.val.val := rfl
  have hc:=couplingCoefficient_factorial q hq hq1 (c:ℤ) p.2.val p.2.val (le_refl _)
  simp only [Nat.sub_self,qfactorial_zero,mul_one] at hc
  rw [mul_div_cancel_right₀ _ (qfactorial_ne_zero q hq p.2.val)] at hc
  change 0 < (-1:ℝ)^(m-t.val.val)*((Real.sqrt (quantumHighestNorm q (coupledLabel l (m+b) p.1) c p.2))⁻¹ *
    couplingCoefficient q (c:ℤ) p.2.val p.2.val *
    standardClebschCoefficient q hq hq1 l (m+b) p.1
      (leftRootIndexPair l (m+b) c p (Fin.last p.2.val)).1 0 (m:ℤ))
  rw [← hr,hc]
  have hsq : (-1:ℝ)^p.2.val*(-1:ℝ)^p.2.val=1 := by rw [← mul_pow];norm_num
  have ha : m=p.1.val+(leftRootIndexPair l (m+b) c p (Fin.last p.2.val)).1.val := by
    have ht:=t.val.isLt
    simp only [p,quantumCupLeftPath,leftRootIndexPair,couplingBasisIndex,Fin.val_last]
    omega
  have hCG:=standardClebschCoefficient_first_closed q hq hq1 l (m+b) p.1
    (leftRootIndexPair l (m+b) c p (Fin.last p.2.val)).1 m ha (by omega)
  rw [hCG]
  have hpos : 0 < (Real.sqrt (quantumHighestNorm q (coupledLabel l (m+b) p.1) c p.2))⁻¹ *
      q^(couplingExponent (c:ℤ) p.2.val p.2.val) *
      ((Real.sqrt (quantumHighestNorm q l (m+b) p.1))⁻¹ *
        q^(-((leftRootIndexPair l (m+b) c p (Fin.last p.2.val)).1.val:ℤ)*(l:ℤ)) *
        qfactorial q ((m+b)-p.1.val) *
        qfactorial q (coupledLabel l (m+b) p.1-(leftRootIndexPair l (m+b) c p (Fin.last p.2.val)).1.val) /
          (qfactorial q (coupledLabel l (m+b) p.1)*qfactorial q ((m+b)-m))) := by
    exact mul_pos
      (mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr (quantumHighestNorm_pos q hq _ _ _))) (zpow_pos hq _))
      (div_pos
        (mul_pos (mul_pos (mul_pos
          (inv_pos.mpr (Real.sqrt_pos.mpr (quantumHighestNorm_pos q hq _ _ _)))
          (zpow_pos hq _)) (qfactorial_pos q hq _)) (qfactorial_pos q hq _))
        (mul_pos (qfactorial_pos q hq _) (qfactorial_pos q hq _)))
  convert hpos using 1 <;> nlinarith [hsq]

end AMSPhysical
#print axioms AMSPhysical.standardCupLeftHighest_first_boundary_signed_pos
#print axioms AMSPhysical.standardCupRightHighest_first_boundary_signed_pos
