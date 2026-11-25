import QuantumMixedNormSlots
import QuantumOccupationCharacter
import QuantumOccupationGraph

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3600000
noncomputable section
namespace AMSPhysical

def mixedNormSummand (q : ℝ) (n a b r : ℕ) (t : occupationWeights (Fin (n+1)) r) : ℝ :=
  q^((a:ℤ)*t.val 0-(b:ℤ)*t.val (Fin.last n)-2*occupationHeightZ n r t)*
    (qfactorial q (a+(t.val 0).toNat)/qfactorial q ((t.val 0).toNat))*
    (qfactorial q (b+(t.val (Fin.last n)).toNat)/qfactorial q ((t.val (Fin.last n)).toNat))

theorem mixedNormSlot_coeff_product (q : ℝ) (hq : 0<q) (n a b r : ℕ) (hn : 0<n)
    (t : occupationWeights (Fin (n+1)) r) :
    (∏ k : Fin (n+1),PowerSeries.coeff ((t.val k).toNat) (mixedNormSlot q a b n k))=
      mixedNormSummand q n a b r t := by
  classical
  let d : Fin (n+1) → ℤ := fun k => -2*(k.val:ℤ)+(if k=0 then (a:ℤ) else 0)-
    (if k=Fin.last n then (b:ℤ) else 0)
  have hn0 : (Fin.last n : Fin (n+1))≠0 := by intro he;have hh := congrArg Fin.val he;simp only [Fin.val_last,Fin.val_zero] at hh;omega
  have hslot (k : Fin (n+1)) :
      PowerSeries.coeff ((t.val k).toNat) (mixedNormSlot q a b n k)=q^(d k*t.val k)*
        (if k=0 then qfactorial q (a+(t.val k).toNat)/qfactorial q ((t.val k).toNat) else 1)*
        (if k=Fin.last n then qfactorial q (b+(t.val k).toNat)/qfactorial q ((t.val k).toNat) else 1) := by
    have htk := Int.toNat_of_nonneg (t.property.1 k)
    by_cases hk0 : k=0
    · subst k
      rw [mixedNormSlot_first_coeff q hq]
      simp only [d,ite_true,if_neg (Ne.symm hn0),Fin.val_zero,Nat.cast_zero,mul_zero,zero_add,sub_zero,mul_one,htk]
      ring
    · by_cases hkn : k=Fin.last n
      · subst k
        rw [mixedNormSlot_last_coeff q hq a b n _ hn]
        simp only [d,if_neg hn0,ite_true,Fin.val_last,add_zero,htk]
        ring
      · rw [mixedNormSlot_interior_coeff q a b n _ k hk0 hkn]
        simp only [d,if_neg hk0,if_neg hkn,add_zero,sub_zero,mul_one,htk]
  have hd : (∑ k : Fin (n+1),d k*t.val k)=
      (a:ℤ)*t.val 0-(b:ℤ)*t.val (Fin.last n)-2*occupationHeightZ n r t := by
    have hs : (∑ k : Fin (n+1),(-2*(k.val:ℤ))*t.val k)= -2*occupationHeightZ n r t := by
      unfold occupationHeightZ latticePairing
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    simp only [d,sub_mul,add_mul,ite_mul,zero_mul,Finset.sum_add_distrib,Finset.sum_sub_distrib]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    rw [hs]
    ring
  simp only [hslot,Finset.prod_mul_distrib]
  rw [← zpow_finset_sum q (ne_of_gt hq) Finset.univ (fun k => d k*t.val k),hd]
  simp only [Finset.prod_ite_eq',Finset.mem_univ,ite_true]
  rfl

end AMSPhysical
#print axioms AMSPhysical.mixedNormSlot_coeff_product
