import WeightedEuler
import FixedEquivalences
import FockOperators

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical
open MvPolynomial

variable {K : Type*} [Field K]

def familyWeight (n : ℕ) (a : Fin 4) (i : Fin 4×Fin n) : K := if i.1=a then 1 else 0

theorem weightedEuler_family (n : ℕ) (a : Fin 4) (p : PN K n) :
    weightedEuler (familyWeight n a) p=eulerFamily n a p := by
  simp [weightedEuler_apply,familyWeight,Fintype.sum_prod_type,eulerFamily]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp

theorem eulerFamily_mixed_pair (n : ℕ) (a v w : Fin 4) (p : PN K n) :
    eulerFamily n a (dotN n v w*lapN n v w p)=
      dotN n v w*lapN n v w (eulerFamily n a p) := by
  simp_rw [← weightedEuler_family]
  simp only [dotN,lapN,Finset.sum_mul,Finset.mul_sum,map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact weightedEuler_balanced_second (familyWeight n a) (v,j) (w,j) (w,i) (v,i)
    (by simp only [familyWeight]; exact add_comm _ _) p

theorem lapN_smul (n : ℕ) (v w : Fin 4) (c : K) (p : PN K n) :
    lapN n v w (c • p)=c • lapN n v w p := by
  simp only [lapN,Derivation.map_smul,Finset.smul_sum]

theorem mixed_pair_preserves_family [CharZero K] (n : ℕ) (v w : Fin 4)
    (r : Fin 4 → ℕ) (p : PN K n) (hp : p∈familySpace n r) :
    dotN n v w*lapN n v w p∈familySpace n r := by
  apply (familySpace_iff_euler n r _).mpr
  intro a
  rw [eulerFamily_mixed_pair,(familySpace_iff_euler n r p).mp hp a,lapN_smul,mul_smul_comm]

theorem mixedXYSource_pullN (n : ℕ) (f : P4 K) :
    dotN n 0 2*lapN n 0 2 (pullN n f)=pullN n (mixedXYSource n f) := by
  rw [radialXY_actual]
  simp only [mixedXYSource,map_mul,pullN_X,coordsN,Matrix.cons_val_zero]

theorem mixedZYSource_pullN (n : ℕ) (f : P4 K) :
    dotN n 1 2*lapN n 1 2 (pullN n f)=pullN n (mixedZYSource n f) := by
  rw [radialZY_actual]
  simp [mixedZYSource,pullN_X,coordsN]

theorem mixedXYSource_preserves [CharZero K] (h : ℕ) (r : Fin 4 → ℕ) (f : P4 K)
    (hf : f∈fixedContractions r) : mixedXYSource (h+2) f∈fixedContractions r := by
  apply (fixedContractions_rank h r _).mpr
  have hp := (fixedContractions_rank h r f).mp hf
  have he := mixed_pair_preserves_family (2+h) 0 2 r _ hp
  rw [mixedXYSource_pullN,Nat.add_comm 2 h] at he
  rw [Nat.add_comm 2 h]
  exact he

theorem mixedZYSource_preserves [CharZero K] (h : ℕ) (r : Fin 4 → ℕ) (f : P4 K)
    (hf : f∈fixedContractions r) : mixedZYSource (h+2) f∈fixedContractions r := by
  apply (fixedContractions_rank h r _).mpr
  have hp := (fixedContractions_rank h r f).mp hf
  have he := mixed_pair_preserves_family (2+h) 1 2 r _ hp
  rw [mixedZYSource_pullN,Nat.add_comm 2 h] at he
  rw [Nat.add_comm 2 h]
  exact he

end AMSPhysical

#print axioms AMSPhysical.mixedXYSource_preserves
#print axioms AMSPhysical.mixedZYSource_preserves
