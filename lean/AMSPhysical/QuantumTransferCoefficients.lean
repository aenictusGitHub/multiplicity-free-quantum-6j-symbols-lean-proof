import QuantumTripleAnnihilation
import QuantumCreationRaisingScalar

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical

theorem tripleRightCoefficient_firstContraction_shift (q : ℝ) (hq : q≠0) (n : ℕ)
    (j : Fin (n+1)) (p : OccupationTripleLattice n) :
    tripleRightCreationCoefficient q n j (p+tripleFirstContractionShift n)=
      q^(if j=0 then 1 else 0:ℤ)*tripleRightCreationCoefficient q n j p := by
  have h:=tripleRightCreationCoefficient_middle_shift q hq n 0 j (-1) p
  have he : j.val ≤ (0:Fin (n+1)).val ↔ j=0 := by
    constructor
    · intro hj;apply Fin.ext;simp only [Fin.val_zero] at hj ⊢;omega
    · rintro rfl;exact le_refl _
  simp only [he] at h
  have hp : -(if j=0 then (-1:ℤ) else 0)=(if j=0 then 1 else 0:ℤ) := by split_ifs <;> ring
  rw [hp] at h
  simpa only [tripleRightCreationCoefficient,tripleFirstContractionShift,Prod.fst_add,Prod.snd_add] using h

theorem tripleRightCoefficient_transfer_shift (q : ℝ) (hq : q≠0) (n : ℕ)
    (j : Fin (n+1)) (p : OccupationTripleLattice n) :
    tripleRightCreationCoefficient q n j (p+tripleTransferShift n)=
      q^(-(if j=0 then 1 else 0:ℤ))*tripleRightCreationCoefficient q n j p := by
  have h:=tripleRightCreationCoefficient_third_shift q hq n 0 j 1 p
  have he : j.val ≤ (0:Fin (n+1)).val ↔ j=0 := by
    constructor
    · intro hj;apply Fin.ext;simp only [Fin.val_zero] at hj ⊢;omega
    · rintro rfl;exact le_refl _
  simpa only [he,tripleRightCreationCoefficient,tripleTransferShift,Prod.fst_add,Prod.snd_add] using h

theorem tripleFirstContractionCoefficient_right_shift (q : ℝ) (n : ℕ)
    (j : Fin (n+1)) (p : OccupationTripleLattice n) :
    tripleFirstContractionCoefficient q n (p+tripleRightCreationShift n j)=
      qInteger q (p.1 0)*qInteger q (p.2.1 0+(if j=0 then 1 else 0)) := by
  simp only [tripleFirstContractionCoefficient,tripleRightCreationShift,Prod.fst_add,Prod.snd_add,
    Pi.add_apply,Pi.zero_apply,add_zero,Pi.single_apply,eq_comm]

theorem tripleTransferCoefficient_right_shift (q : ℝ) (hq : q≠0) (n : ℕ)
    (j : Fin (n+1)) (p : OccupationTripleLattice n) :
    tripleTransferCoefficient q n (p+tripleRightCreationShift n j)=
      q^(-2-(if j=0 then 1 else 0:ℤ))*tripleTransferCoefficient q n p := by
  unfold tripleTransferCoefficient tripleRightCreationShift
  simp only [Prod.fst_add,Prod.snd_add,Pi.add_apply,Pi.zero_apply,add_zero,Pi.single_apply,
    Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  simp only [show ((0:Fin (n+1))=j) ↔ j=0 from eq_comm]
  have he : -(n:ℤ)-((∑ i : Fin (n+1),p.2.1 i)+1)-((∑ i : Fin (n+1),p.2.2 i)+1)-
      (p.2.1 0+(if j=0 then 1 else 0:ℤ))=
      (-2-(if j=0 then 1 else 0:ℤ))+
        (-(n:ℤ)-(∑ i : Fin (n+1),p.2.1 i)-(∑ i : Fin (n+1),p.2.2 i)-p.2.1 0) := by ring
  rw [he,zpow_add₀ hq]
  ring

theorem tripleFirstContraction_cross_coefficient (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (n : ℕ) (p : OccupationTripleLattice n) :
    tripleRightCreationCoefficient q n 0 p*tripleFirstContractionCoefficient q n (p+tripleRightCreationShift n 0)-
      tripleFirstContractionCoefficient q n p*tripleRightCreationCoefficient q n 0 (p+tripleFirstContractionShift n)=
        tripleTransferCoefficient q n p := by
  rw [tripleFirstContractionCoefficient_right_shift,tripleRightCoefficient_firstContraction_shift q hq,
    if_pos rfl,zpow_one,tripleRightCreationCoefficient_zero]
  unfold tripleFirstContractionCoefficient tripleTransferCoefficient
  have hp : q^(-(n:ℤ)-(∑ i : Fin (n+1),p.2.1 i)-(∑ i : Fin (n+1),p.2.2 i))*q^(-p.2.1 0)=
      q^(-(n:ℤ)-(∑ i : Fin (n+1),p.2.1 i)-(∑ i : Fin (n+1),p.2.2 i)-p.2.1 0) := by
    rw [← zpow_add₀ hq]
    congr 1
  calc
    _ = qInteger q (p.1 0)*(-1:ℝ)^n*
      (q^(-(n:ℤ)-(∑ i : Fin (n+1),p.2.1 i)-(∑ i : Fin (n+1),p.2.2 i))*q^(-p.2.1 0)) := by
        linear_combination (qInteger q (p.1 0)*(-1:ℝ)^n*
          q^(-(n:ℤ)-(∑ i : Fin (n+1),p.2.1 i)-(∑ i : Fin (n+1),p.2.2 i)))*qInteger_succ_sub q hq hD (p.2.1 0)
    _ = _ := by rw [hp]

end AMSPhysical
