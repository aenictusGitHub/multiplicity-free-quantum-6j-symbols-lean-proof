import QuantumMixedAnnihilationCoefficients
import QuantumRadialDiagonalSum
import QuantumDimensionProductIdentity

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical

theorem mixedCreationCoefficient_self_annihilation_cancel (q : ℝ) (hq : q≠0) (n : ℕ)
    (i : Fin (n+1)) (p : OccupationPairLattice n) :
    q^(-2:ℤ)*mixedCreationCoefficient q n i (p-mixedCreationShift n i)=mixedCreationCoefficient q n i p := by
  rw [mixedCreationCoefficient_annihilation_shift q hq]
  simp only [le_refl,ite_true,mul_one]
  rw [← mul_assoc,← zpow_add₀ hq]
  norm_num

theorem mixedAnnihilationCoefficient_self_creation (q : ℝ) (n : ℕ)
    (i : Fin (n+1)) (p : OccupationPairLattice n) :
    mixedAnnihilationCoefficient q n i (p+mixedCreationShift n i)=
      (-1:ℝ)^i.val*q^(-(i.val:ℤ)-occupationStrictPrefix n i p.1-occupationStrictPrefix n i p.2)*
        qInteger q (p.1 i+1)*qInteger q (p.2 i+1) := by
  unfold mixedAnnihilationCoefficient mixedCreationShift
  change (-1:ℝ)^i.val*q^(-(i.val:ℤ)-occupationStrictPrefix n i (p.1+Pi.single i 1)-
    occupationStrictPrefix n i (p.2+Pi.single i 1))*
    qInteger q ((p.1+Pi.single i 1 : Fin (n+1) → ℤ) i)*
    qInteger q ((p.2+Pi.single i 1 : Fin (n+1) → ℤ) i)=_
  simp only [occupationStrictPrefix_add,occupationStrictPrefix_self_single,add_zero,Pi.add_apply,Pi.single_eq_same]

theorem mixedCreationAnnihilation_diagonal_factor (q : ℝ) (hq : q≠0) (n : ℕ)
    (i : Fin (n+1)) (p : OccupationPairLattice n) :
    mixedCreationCoefficient q n i p*
      ((-1:ℝ)^i.val*q^(-(i.val:ℤ)-occupationStrictPrefix n i p.1-occupationStrictPrefix n i p.2))=
      q^(-2*(i.val:ℤ)-2*occupationStrictPrefix n i p.1-2*occupationStrictPrefix n i p.2-p.1 i-p.2 i) := by
  have hs : (-1:ℝ)^i.val*(-1:ℝ)^i.val=1 := by rw [← mul_pow];norm_num
  unfold mixedCreationCoefficient
  simp only [occupationPrefix_strict]
  have hp : q^(-(i.val:ℤ)-(occupationStrictPrefix n i p.1+p.1 i)-(occupationStrictPrefix n i p.2+p.2 i))*
      q^(-(i.val:ℤ)-occupationStrictPrefix n i p.1-occupationStrictPrefix n i p.2)=
      q^(-2*(i.val:ℤ)-2*occupationStrictPrefix n i p.1-2*occupationStrictPrefix n i p.2-p.1 i-p.2 i) := by
    rw [← zpow_add₀ hq]
    congr 1
    ring
  calc
    _ = ((-1:ℝ)^i.val*(-1:ℝ)^i.val)*
        (q^(-(i.val:ℤ)-(occupationStrictPrefix n i p.1+p.1 i)-(occupationStrictPrefix n i p.2+p.2 i))*
          q^(-(i.val:ℤ)-occupationStrictPrefix n i p.1-occupationStrictPrefix n i p.2)) := by ring
    _ = _ := by rw [hs,one_mul,hp]

theorem mixedOscillator_diagonal_coefficient (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n : ℕ)
    (i : Fin (n+1)) (p : OccupationPairLattice n) :
    mixedCreationCoefficient q n i p*mixedAnnihilationCoefficient q n i (p+mixedCreationShift n i)-
      q^(-2:ℤ)*mixedAnnihilationCoefficient q n i p*mixedCreationCoefficient q n i (p-mixedCreationShift n i)=
      mixedRadialDiagonalCoefficient q n i p := by
  have hi : qInteger q (p.1 i+1)*qInteger q (p.2 i+1)-qInteger q (p.1 i)*qInteger q (p.2 i)=
      qInteger q (p.1 i+p.2 i+1) := by
    have h:=qInteger_shift_product q hq (p.1 i) (p.2 i) 1
    rw [qInteger_one q hD,one_mul] at h
    exact h
  rw [mixedAnnihilationCoefficient_self_creation]
  have he : q^(-2:ℤ)*mixedAnnihilationCoefficient q n i p*mixedCreationCoefficient q n i (p-mixedCreationShift n i)=
      mixedAnnihilationCoefficient q n i p*mixedCreationCoefficient q n i p := by
    calc
      _ = mixedAnnihilationCoefficient q n i p*(q^(-2:ℤ)*mixedCreationCoefficient q n i (p-mixedCreationShift n i)) := by ring
      _ = _ := by rw [mixedCreationCoefficient_self_annihilation_cancel q hq]
  rw [he]
  unfold mixedAnnihilationCoefficient
  calc
    _ = (mixedCreationCoefficient q n i p*((-1:ℝ)^i.val*
        q^(-(i.val:ℤ)-occupationStrictPrefix n i p.1-occupationStrictPrefix n i p.2)))*
        (qInteger q (p.1 i+1)*qInteger q (p.2 i+1)-qInteger q (p.1 i)*qInteger q (p.2 i)) := by ring
    _ = _ := by rw [mixedCreationAnnihilation_diagonal_factor q hq,hi];rfl

theorem mixedOscillator_offdiagonal_coefficient (q : ℝ) (hq : q≠0) (n : ℕ)
    (i j : Fin (n+1)) (hij : i≠j) (p : OccupationPairLattice n) :
    mixedCreationCoefficient q n j p*mixedAnnihilationCoefficient q n i (p+mixedCreationShift n j)-
      q^(-2:ℤ)*mixedAnnihilationCoefficient q n i p*mixedCreationCoefficient q n j (p-mixedCreationShift n i)=0 := by
  rw [mixedAnnihilationCoefficient_other_creation q hq n i j hij,mixedCreationCoefficient_annihilation_shift q hq]
  by_cases hji : j.val < i.val
  · have hij' : ¬ i.val ≤ j.val := by omega
    simp only [if_pos hji,if_neg hij',mul_one,mul_zero,zpow_zero,mul_one]
    ring
  · have hij' : i.val ≤ j.val := by omega
    simp only [if_neg hji,if_pos hij',mul_zero,mul_one,zpow_zero,one_mul]
    have hp : q^(-2:ℤ)*q^(2:ℤ)=1 := by rw [← zpow_add₀ hq];norm_num
    linear_combination -(mixedAnnihilationCoefficient q n i p*mixedCreationCoefficient q n j p)*hp

end AMSPhysical
