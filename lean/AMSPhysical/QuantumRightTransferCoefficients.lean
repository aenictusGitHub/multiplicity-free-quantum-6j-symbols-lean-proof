import QuantumRightTransferDefinitions

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical

theorem tripleLastPrefactor_left_shift (q : ℝ) (hq : q≠0) (n : ℕ)
    (j : Fin (n+1)) (p : OccupationTripleLattice n) :
    tripleLastContractionPrefactor q n (p+tripleLeftCreationShift n j)=
      q^(-1+(if j=0 then 1 else 0:ℤ))*tripleLastContractionPrefactor q n p := by
  unfold tripleLastContractionPrefactor tripleLeftCreationShift
  simp only [Prod.fst_add,Prod.snd_add,Pi.add_apply,Pi.zero_apply,add_zero,Pi.single_apply,
    Finset.sum_add_distrib,Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  simp only [show ((0:Fin (n+1))=j) ↔ j=0 from eq_comm]
  have he : -(n:ℤ)-((∑ i : Fin (n+1),p.2.1 i)+1)-(∑ i : Fin (n+1),p.2.2 i)+
      (p.2.1 0+(if j=0 then 1 else 0:ℤ))+p.2.2 0=
      (-1+(if j=0 then 1 else 0:ℤ))+
        (-(n:ℤ)-(∑ i : Fin (n+1),p.2.1 i)-(∑ i : Fin (n+1),p.2.2 i)+p.2.1 0+p.2.2 0) := by ring
  rw [he,zpow_add₀ hq]
  ring

theorem tripleLeftCoefficient_lastContraction_shift (q : ℝ) (hq : q≠0) (n : ℕ)
    (j : Fin (n+1)) (p : OccupationTripleLattice n) :
    tripleLeftCreationCoefficient q n j (p+tripleLastContractionShift n)=q*tripleLeftCreationCoefficient q n j p := by
  have h:=mixedCreationCoefficient_second_single_shift q hq n j 0 (-1) (p.1,p.2.1)
  simpa only [Fin.val_zero,Nat.zero_le,ite_true,neg_neg,zpow_one,
    tripleLeftCreationCoefficient,tripleLastContractionShift,mixedCreationCoefficient,
    Prod.fst_add,Prod.snd_add,add_zero] using h

theorem tripleLeftCoefficient_reverseTransfer_shift (q : ℝ) (hq : q≠0) (n : ℕ)
    (j : Fin (n+1)) (p : OccupationTripleLattice n) :
    tripleLeftCreationCoefficient q n j (p+tripleReverseTransferShift n)=q^(-1:ℤ)*tripleLeftCreationCoefficient q n j p := by
  have h:=mixedCreationCoefficient_first_single_shift q hq n j 0 1 (p.1,p.2.1)
  simpa only [Fin.val_zero,Nat.zero_le,ite_true,
    tripleLeftCreationCoefficient,tripleReverseTransferShift,mixedCreationCoefficient,
    Prod.fst_add,Prod.snd_add,add_zero] using h

theorem tripleReverseTransferCoefficient_left_shift (q : ℝ) (hq : q≠0) (n : ℕ)
    (j : Fin (n+1)) (p : OccupationTripleLattice n) :
    tripleReverseTransferCoefficient q n (p+tripleLeftCreationShift n j)=
      q^(-1:ℤ)*tripleReverseTransferCoefficient q n p := by
  unfold tripleReverseTransferCoefficient
  rw [tripleLastPrefactor_left_shift q hq]
  simp only [tripleLeftCreationShift,Prod.fst_add,Prod.snd_add,Pi.add_apply,Pi.single_apply,Pi.zero_apply,add_zero]
  simp only [show ((0:Fin (n+1))=j) ↔ j=0 from eq_comm]
  have hp : q^(-1+(if j=0 then 1 else 0:ℤ))*q^(-(p.1 0+(if j=0 then 1 else 0:ℤ)))=
      q^(-1:ℤ)*q^(-p.1 0) := by
    simp only [← zpow_add₀ hq]
    congr 1
    ring
  linear_combination (tripleLastContractionPrefactor q n p*qInteger q (p.2.2 0))*hp

theorem qInteger_succ_sub_inverse (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (a : ℤ) :
    qInteger q (a+1)-q^(-1:ℤ)*qInteger q a=q^a := by
  rw [qInteger_add q hq a 1,qInteger_one q hD,mul_one]
  ring

theorem tripleLastContraction_cross_coefficient (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (n : ℕ) (p : OccupationTripleLattice n) :
    tripleLeftCreationCoefficient q n 0 p*tripleLastContractionCoefficient q n (p+tripleLeftCreationShift n 0)-
      q^(-2:ℤ)*tripleLastContractionCoefficient q n p*tripleLeftCreationCoefficient q n 0 (p+tripleLastContractionShift n)=
        tripleReverseTransferCoefficient q n p := by
  rw [tripleLeftCoefficient_lastContraction_shift q hq]
  simp only [tripleLastContractionCoefficient]
  rw [tripleLastPrefactor_left_shift q hq]
  simp only [
    if_pos rfl,ite_true,neg_add_cancel,zpow_zero,one_mul,tripleLeftCreationShift,Prod.fst_add,Prod.snd_add,
    Pi.add_apply,Pi.single_eq_same,Pi.zero_apply,add_zero]
  have hQ : q^(-2:ℤ)*q=q^(-1:ℤ) := by
    calc
      _ = q^(-2:ℤ)*q^(1:ℤ) := by rw [zpow_one]
      _ = _ := by rw [← zpow_add₀ hq];norm_num
  have hp : tripleLeftCreationCoefficient q n 0 p*q^(p.2.1 0)=q^(-p.1 0) := by
    rw [tripleLeftCreationCoefficient_zero,← zpow_add₀ hq]
    congr 1
    ring
  calc
    _ = tripleLastContractionPrefactor q n p*tripleLeftCreationCoefficient q n 0 p*qInteger q (p.2.2 0)*
      (qInteger q (p.2.1 0+1)-q^(-1:ℤ)*qInteger q (p.2.1 0)) := by
        linear_combination -(tripleLastContractionPrefactor q n p*tripleLeftCreationCoefficient q n 0 p*
          qInteger q (p.2.1 0)*qInteger q (p.2.2 0))*hQ
    _ = tripleLastContractionPrefactor q n p*(tripleLeftCreationCoefficient q n 0 p*q^(p.2.1 0))*qInteger q (p.2.2 0) := by
      rw [qInteger_succ_sub_inverse q hq hD]
      ring
    _ = _ := by rw [hp];rfl

end AMSPhysical
