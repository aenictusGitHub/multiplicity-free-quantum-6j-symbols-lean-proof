import QuantumClebsch

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
noncomputable section
namespace AMSPhysical
open Module
open scoped TensorProduct

def descendantIndex (a k : ℕ) (u : ℤ) : ℕ := ((k:ℤ)+(a:ℤ)-u).toNat

def DescendantAdmissible (a k : ℕ) (u : ℤ) : Prop :=
  0≤(k:ℤ)+(a:ℤ)-u ∧ (k:ℤ)+(a:ℤ)-u≤(a:ℤ)

instance descendantAdmissible_decidable (a k : ℕ) (u : ℤ) : Decidable (DescendantAdmissible a k u) := by
  unfold DescendantAdmissible
  infer_instance

theorem tensorCoefficient_inner_collapse (r a k : ℕ) (u v : ℤ)
    (huv : u+v=(r:ℤ)+(a:ℤ)) (f : ℕ → ℝ) :
    tensorCoefficient u v (∑ t∈Finset.range (a+1),f t •
      tensorWeightBasis ((k:ℤ)+((a-t:ℕ):ℤ)) ((r:ℤ)-(k:ℤ)+(t:ℤ)))=
      if DescendantAdmissible a k u then f (descendantIndex a k u) else 0 := by
  classical
  rw [map_sum]
  simp only [map_smul,tensorCoefficient_basis,smul_eq_mul]
  by_cases ht : DescendantAdmissible a k u
  · rw [if_pos ht]
    let z := descendantIndex a k u
    have hzi : (z:ℤ)=(k:ℤ)+(a:ℤ)-u := by dsimp [z,descendantIndex];have h0 := ht.1;omega
    have hza : z≤a := by have h0 := ht.2;omega
    rw [Finset.sum_eq_single z]
    · have hfirst : (k:ℤ)+((a-z:ℕ):ℤ)=u := by omega
      have hsecond : (r:ℤ)-(k:ℤ)+(z:ℤ)=v := by omega
      rw [if_pos hfirst,if_pos hsecond,one_mul,mul_one]
    · intro t htr htz
      have hta : t≤a := by have hh := Finset.mem_range.mp htr;omega
      have hfirst : (k:ℤ)+((a-t:ℕ):ℤ)≠u := by intro he;apply htz;omega
      rw [if_neg hfirst,zero_mul,mul_zero]
    · intro hz
      exact (hz (Finset.mem_range.mpr (by omega))).elim
  · rw [if_neg ht]
    apply Finset.sum_eq_zero
    intro t htr
    have hta : t≤a := by have hh := Finset.mem_range.mp htr;omega
    have hfirst : (k:ℤ)+((a-t:ℕ):ℤ)≠u := by
      intro he
      apply ht
      unfold DescendantAdmissible
      constructor <;> omega
    rw [if_neg hfirst,zero_mul,mul_zero]

theorem tensorCoefficient_double_collapse (r a : ℕ) (u v : ℤ)
    (huv : u+v=(r:ℤ)+(a:ℤ)) (f : ℕ → ℕ → ℝ) :
    tensorCoefficient u v (∑ k∈Finset.range (r+1),∑ t∈Finset.range (a+1),f k t •
      tensorWeightBasis ((k:ℤ)+((a-t:ℕ):ℤ)) ((r:ℤ)-(k:ℤ)+(t:ℤ)))=
      ∑ k∈Finset.range (r+1),if DescendantAdmissible a k u then f k (descendantIndex a k u) else 0 := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  exact tensorCoefficient_inner_collapse r a k u v huv (f k)

theorem tensorCoefficient_double_weight_mismatch (r a : ℕ) (u v : ℤ)
    (huv : u+v≠(r:ℤ)+(a:ℤ)) (f : ℕ → ℕ → ℝ) :
    tensorCoefficient (K:=ℝ) u v (∑ k∈Finset.range (r+1),∑ t∈Finset.range (a+1),f k t •
      tensorWeightBasis ((k:ℤ)+((a-t:ℕ):ℤ)) ((r:ℤ)-(k:ℤ)+(t:ℤ)))=0 := by
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro k hk
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro t ht
  have hta : t≤a := by have hh := Finset.mem_range.mp ht;omega
  rw [map_smul,tensorCoefficient_basis,smul_eq_mul]
  by_cases hfirst : (k:ℤ)+((a-t:ℕ):ℤ)=u
  · have hsecond : (r:ℤ)-(k:ℤ)+(t:ℤ)≠v := by intro he;apply huv;omega
    rw [if_neg hsecond,mul_zero,mul_zero]
  · rw [if_neg hfirst,zero_mul,mul_zero]

end AMSPhysical

#print axioms AMSPhysical.tensorCoefficient_double_collapse
