import SpinRacahFactorialSum
import AMSGeneral

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3000000
noncomputable section
namespace AMSPhysical

def quantumFactorialInt (q : ℝ) (z : ℤ) : ℝ := qfactorial q z.toNat

def physicalRacahOffsets (u r A B M S : ℕ) : AMSGeneral.Offsets where
  a := B
  b := r
  c := u
  d := A
  e := (S:ℤ)-(u:ℤ)
  f := (M:ℤ)-(u:ℤ)

theorem physicalRacah_support (u r A B M S k : ℕ) :
    (k:ℤ)∈AMSGeneral.support (physicalRacahOffsets u r A B M S) ↔
      RacahTermAdmissible u r A B M S k := by
  unfold AMSGeneral.support physicalRacahOffsets RacahTermAdmissible
  simp only [Finset.mem_Icc,le_max_iff,max_le_iff,le_min_iff]
  omega

theorem physicalRacah_support_nonnegative (u r A B M S : ℕ) (z : ℤ)
    (hz : z∈AMSGeneral.support (physicalRacahOffsets u r A B M S)) : 0≤z := by
  unfold AMSGeneral.support at hz
  simp only [Finset.mem_Icc,max_le_iff] at hz
  omega

theorem minusOne_zpow_sub_nat (p k : ℕ) :
    (-1:ℝ)^((p:ℤ)-(k:ℤ))=(-1:ℝ)^p*(-1:ℝ)^k := by
  rw [zpow_sub₀ (by norm_num : (-1:ℝ)≠0),zpow_natCast,zpow_natCast,div_eq_mul_inv,← inv_pow]
  norm_num

/-- The independently derived physical rank-two factorial sum is precisely
the scalar kernel used in AMS, with its phase and finite support retained. -/
theorem factorialRacahSum_AMS_series (q : ℝ) (u r A B M S T P : ℕ) (hT : u≤T) :
    AMSGeneral.series (quantumFactorialInt q) P T (physicalRacahOffsets u r A B M S)=
      (-1:ℝ)^P*(∑ k∈Finset.range (u+1),factorialRacahTerm q u r A B M S T k) := by
  classical
  unfold AMSGeneral.series
  simp only [factorialRacahTerm]
  rw [← Finset.sum_filter,Finset.mul_sum]
  apply Finset.sum_bij (fun z _ => z.toNat)
  · intro z hz
    have hnonneg := physicalRacah_support_nonnegative u r A B M S z hz
    have hcast : (z.toNat:ℤ)=z := Int.toNat_of_nonneg hnonneg
    have hadm : RacahTermAdmissible u r A B M S z.toNat := by
      apply (physicalRacah_support u r A B M S z.toNat).mp
      rw [hcast]
      exact hz
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr (by have hh := hadm.1;omega),hadm⟩
  · intro z hz w hw he
    have hz0 := physicalRacah_support_nonnegative u r A B M S z hz
    have hw0 := physicalRacah_support_nonnegative u r A B M S w hw
    omega
  · intro k hk
    have hh := Finset.mem_filter.mp hk
    refine ⟨(k:ℤ),(physicalRacah_support u r A B M S k).mpr hh.2,?_⟩
    simp
  · intro z hz
    have hnonneg := physicalRacah_support_nonnegative u r A B M S z hz
    have hcast : (z.toNat:ℤ)=z := Int.toNat_of_nonneg hnonneg
    have hadm : RacahTermAdmissible u r A B M S z.toNat := by
      apply (physicalRacah_support u r A B M S z.toNat).mp
      rw [hcast]
      exact hz
    rcases hadm with ⟨hku,hkr,hkA,hkB,hkM,hkS⟩
    have h₁ : ((T:ℤ)-z).toNat=T-z.toNat := by omega
    have h₂ : ((B:ℤ)-z).toNat=B-z.toNat := by omega
    have h₃ : ((r:ℤ)-z).toNat=r-z.toNat := by omega
    have h₄ : ((u:ℤ)-z).toNat=u-z.toNat := by omega
    have h₅ : ((A:ℤ)-z).toNat=A-z.toNat := by omega
    have h₆ : ((S:ℤ)-(u:ℤ)+z).toNat=S-(u-z.toNat) := by omega
    have h₇ : ((M:ℤ)-(u:ℤ)+z).toNat=M-(u-z.toNat) := by omega
    unfold physicalRacahOffsets quantumFactorialInt
    simp only [h₁,h₂,h₃,h₄,h₅,h₆,h₇]
    have hphase : (-1:ℝ)^((P:ℤ)-z)=(-1:ℝ)^P*(-1:ℝ)^z.toNat := by
      rw [← hcast]
      simp only [Int.toNat_natCast,minusOne_zpow_sub_nat]
    rw [hphase]
    ring

end AMSPhysical

#print axioms AMSPhysical.factorialRacahSum_AMS_series
