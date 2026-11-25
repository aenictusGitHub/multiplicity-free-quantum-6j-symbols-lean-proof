import QuantumMixedCreationCoefficients

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical

theorem qInteger_succ_sub (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (a : ℤ) :
    qInteger q (a+1)-q*qInteger q a=q^(-a) := by
  have h := qInteger_add q hq 1 a
  rw [qInteger_one q hD,zpow_one,mul_one] at h
  rw [add_comm a 1,h]
  ring

theorem qInteger_mul_succ_sub (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (a : ℤ) :
    q*qInteger q (a+1)-qInteger q a=q^(a+1) := by
  have h := qInteger_add q hq a 1
  rw [qInteger_one q hD,zpow_neg_one,mul_one] at h
  rw [h,zpow_add₀ hq,zpow_one]
  field_simp
  ring

def pairRaisingFirstWeight (q : ℝ) (n : ℕ) (i : Fin n) (p : OccupationPairLattice n) : ℝ :=
  qInteger q (p.1 i.succ)*q^(-simpleOccupationWeight n p.2 i)

def pairRaisingSecondWeight (q : ℝ) (n : ℕ) (i : Fin n) (p : OccupationPairLattice n) : ℝ :=
  qInteger q (p.2 i.castSucc)

theorem simpleOccupationWeight_add_single (n : ℕ) (i : Fin n) (k : Fin (n+1))
    (x : Fin (n+1) → ℤ) :
    simpleOccupationWeight n (x+Pi.single k 1) i=
      simpleOccupationWeight n x i+(if k=i.castSucc then 1 else 0)-(if k=i.succ then 1 else 0) := by
  simp only [simpleOccupationWeight,Pi.add_apply,Pi.single_apply]
  split_ifs <;> omega

theorem pairRaisingFirstWeight_creation_shift (q : ℝ) (n : ℕ) (i : Fin n)
    (k : Fin (n+1)) (p : OccupationPairLattice n) :
    pairRaisingFirstWeight q n i (p+mixedCreationShift n k)=
      qInteger q (p.1 i.succ+(if k=i.succ then 1 else 0))*
        q^(-simpleOccupationWeight n p.2 i-(if k=i.castSucc then 1 else 0)+(if k=i.succ then 1 else 0)) := by
  unfold pairRaisingFirstWeight mixedCreationShift
  change qInteger q ((p.1+Pi.single k 1 : Fin (n+1) → ℤ) i.succ)*q^(-simpleOccupationWeight n (p.2+Pi.single k 1) i)=_
  rw [simpleOccupationWeight_add_single]
  simp only [Pi.add_apply,Pi.single_apply,eq_comm]
  congr 1
  congr 1
  ring

theorem pairRaisingSecondWeight_creation_shift (q : ℝ) (n : ℕ) (i : Fin n)
    (k : Fin (n+1)) (p : OccupationPairLattice n) :
    pairRaisingSecondWeight q n i (p+mixedCreationShift n k)=
      qInteger q (p.2 i.castSucc+(if k=i.castSucc then 1 else 0)) := by
  simp only [pairRaisingSecondWeight,mixedCreationShift,Prod.fst_add,Prod.snd_add,Pi.add_apply,Pi.single_apply,eq_comm]

/-- Each first-leg creation commutator vanishes except at the right endpoint. -/
theorem mixedCreation_raising_first_coefficient (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (n : ℕ) (i : Fin n) (k : Fin (n+1)) (p : OccupationPairLattice n) :
    pairRaisingFirstWeight q n i p*
        mixedCreationCoefficient q n k (p+(latticeRoot i.castSucc i.succ,0))-
      mixedCreationCoefficient q n k p*pairRaisingFirstWeight q n i (p+mixedCreationShift n k)=
      if k=i.succ then -mixedCreationCoefficient q n k p*q^(p.1 i.succ+1-simpleOccupationWeight n p.2 i) else 0 := by
  rw [mixedCreationCoefficient_first_root q hq,pairRaisingFirstWeight_creation_shift]
  have hij := typeA_root_endpoints n i
  by_cases hi : k=i.castSucc
  · subst k
    simp only [ite_true,if_neg hij,neg_zero,zpow_neg_one,add_zero,sub_zero,pairRaisingFirstWeight]
    rw [zpow_sub₀ hq,zpow_one]
    ring
  · by_cases hj : k=i.succ
    · subst k
      simp only [if_neg (Ne.symm hij),ite_true,neg_zero,zpow_zero,sub_zero,mul_one,pairRaisingFirstWeight]
      have hp : q^(-simpleOccupationWeight n p.2 i+1)=q*q^(-simpleOccupationWeight n p.2 i) := by
        rw [zpow_add₀ hq,zpow_one,mul_comm]
      have ht : q^(p.1 i.succ+1-simpleOccupationWeight n p.2 i)=q^(p.1 i.succ+1)*q^(-simpleOccupationWeight n p.2 i) := by
        rw [sub_eq_add_neg,zpow_add₀ hq]
      rw [hp,ht]
      linear_combination -(mixedCreationCoefficient q n i.succ p*q^(-simpleOccupationWeight n p.2 i))*
        qInteger_mul_succ_sub q hq hD (p.1 i.succ)
    · simp [hi,hj,pairRaisingFirstWeight]
      ring

/-- Each second-leg commutator vanishes except at the left endpoint. -/
theorem mixedCreation_raising_second_coefficient (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (n : ℕ) (i : Fin n) (k : Fin (n+1)) (p : OccupationPairLattice n) :
    pairRaisingSecondWeight q n i p*
        mixedCreationCoefficient q n k (p+(0,-latticeRoot i.castSucc i.succ))-
      mixedCreationCoefficient q n k p*pairRaisingSecondWeight q n i (p+mixedCreationShift n k)=
      if k=i.castSucc then -mixedCreationCoefficient q n k p*q^(-p.2 i.castSucc) else 0 := by
  rw [mixedCreationCoefficient_second_negative_root q hq,pairRaisingSecondWeight_creation_shift]
  by_cases hi : k=i.castSucc
  · subst k
    simp only [ite_true,zpow_one,pairRaisingSecondWeight]
    linear_combination -(mixedCreationCoefficient q n i.castSucc p)*qInteger_succ_sub q hq hD (p.2 i.castSucc)
  · simp [hi,pairRaisingSecondWeight]
    ring

end AMSPhysical
