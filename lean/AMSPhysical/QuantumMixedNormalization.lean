import QuantumMixedNormClosed
import QuantumPureOccupationNorms
import QuantumMixedHighest
import QuantumMixedWeight

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

theorem mixedHighestCoefficient_highest (q : ℝ) (hq : 0<q) (n r b : ℕ) (hn : 0<n) :
    mixedHighestCoefficient q n r b (highestOccupation n r)=1 := by
  have hlast : (highestOccupation n r).val (Fin.last n)=0 := by
    have hn0 : (Fin.last n : Fin (n+1))≠0 := by
      intro he
      have hh := congrArg Fin.val he
      simp only [Fin.val_last,Fin.val_zero] at hh
      omega
    simp [highestOccupation,Pi.single_apply,hn0,Ne.symm hn0]
  unfold mixedHighestCoefficient
  rw [pureOccupation_height n r 0 _ rfl,occupationCompactWeight_highest q hq,hlast]
  simp

theorem mixedCouplingNormClosed_pos (q : ℝ) (hq : 0<q) (n a b r : ℕ) :
    0<mixedCouplingNormClosed q n a b r := by
  unfold mixedCouplingNormClosed
  exact div_pos
    (mul_pos (mul_pos (mul_pos (mul_pos (zpow_pos hq _) (qfactorial_pos q hq r))
      (qfactorial_pos q hq a)) (qfactorial_pos q hq b)) (qfactorial_pos q hq (a+n+b+r)))
    (mul_pos (mul_pos (qfactorial_pos q hq (r+a)) (qfactorial_pos q hq (r+b)))
      (qfactorial_pos q hq (a+n+b)))

def normalizedMixedHighestVector (q : ℝ) (n r a b : ℕ) :=
  (Real.sqrt (mixedCouplingNormClosed q n a b r))⁻¹ • mixedHighestVector q n r a b

/-- The explicitly normalized higher-rank coupling vector has actual norm one. -/
theorem normalizedMixedHighestVector_norm_one (q : ℝ) (hq : 0<q) (n a b r : ℕ) (hn : 0<n) :
    mixedTensorBilin q n (r+a) (r+b) (normalizedMixedHighestVector q n r a b)
      (normalizedMixedHighestVector q n r a b)=1 := by
  unfold normalizedMixedHighestVector
  simp only [map_smul,LinearMap.smul_apply,Pi.smul_apply,smul_eq_mul]
  rw [mixedHighestVector_norm_closed q hq n a b r hn]
  have hp := mixedCouplingNormClosed_pos q hq n a b r
  have hs := Real.sq_sqrt hp.le
  have hs0 := ne_of_gt (Real.sqrt_pos.mpr hp)
  field_simp [hs0]
  nlinarith

theorem normalizedMixedHighestVector_E_zero (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n r a b : ℕ) (i : Fin n) :
    typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n (r+a) (r+b)
      (typeAAlgebraGenerator q n i 0) (normalizedMixedHighestVector q n r a b)=0 := by
  unfold normalizedMixedHighestVector
  rw [map_smul,mixedHighestVector_E_zero q hq hq1 n r a b i,smul_zero]

theorem normalizedMixedHighestVector_K (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (n r a b : ℕ) (i : Fin n) :
    typeAMixedTensor q hq hD n (r+a) (r+b) (typeAAlgebraGenerator q n i 2)
      (normalizedMixedHighestVector q n r a b)=
      q^(mixedHighestDynkin n a b i) • normalizedMixedHighestVector q n r a b := by
  unfold normalizedMixedHighestVector
  rw [map_smul,mixedHighestVector_K,smul_comm]

end AMSPhysical
#print axioms AMSPhysical.normalizedMixedHighestVector_norm_one
