import QuantumPowers
import Mathlib.Data.Finset.Max

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical

variable {K : Type*} [Field K]

/-- Irreducibility of the independently constructed highest-weight module.
Only the standard nonvanishing condition on quantum integers is needed. -/
theorem quantumEF_irreducible (q : K) (l : ℕ)
    (hq : ∀ j : ℤ,0<j → j≤(l:ℤ) → qInteger q j≠0)
    (S : Submodule K (WeightModule K)) (hS : S≤finiteWeightSpace l)
    (hE : ∀ p∈S,quantumE q p∈S) (hF : ∀ p∈S,quantumF q l p∈S) :
    S=⊥ ∨ S=finiteWeightSpace l := by
  classical
  by_cases hzero : S=⊥
  · exact Or.inl hzero
  right
  have hex : ∃ p∈S,p≠0 := by
    by_contra hn
    push_neg at hn
    apply hzero
    apply le_antisymm _ bot_le
    intro p hp
    simpa only [Submodule.mem_bot] using hn p hp
  obtain ⟨p,hp,hp0⟩ := hex
  have hsupp := Finsupp.support_nonempty_iff.mpr hp0
  let m : ℤ := p.support.max' hsupp
  have hm : m∈p.support := Finset.max'_mem _ _
  have hmb := (hS hp) hm
  have hm0 : 0≤m := hmb.1
  have hml : m≤(l:ℤ) := hmb.2
  have hmnat : (m.toNat:ℤ)=m := Int.toNat_of_nonneg hm0
  have htop : ∀ k∈p.support,0≤k ∧ k≤(m.toNat:ℤ) := by
    intro k hk
    refine ⟨((hS hp) hk).1,?_⟩
    rw [hmnat]
    exact Finset.le_max' _ _ hk
  have hpow := end_power_preserves S (quantumE q) hE p hp m.toNat
  rw [quantumE_power_top q p m.toNat htop,hmnat] at hpow
  have hcoeff : p m*qFalling q m m.toNat≠0 :=
    mul_ne_zero (Finsupp.mem_support_iff.mp hm)
      (qFalling_ne_zero q m m.toNat (by omega) (fun j hj hjm => hq j hj (hjm.trans hml)))
  have hhigh : Finsupp.single (0:ℤ) (1:K)∈S := by
    have he : Finsupp.single (0:ℤ) (p m*qFalling q m m.toNat)=
        (p m*qFalling q m m.toNat) • Finsupp.single (0:ℤ) (1:K) := by
      simp only [Finsupp.smul_single,smul_eq_mul,mul_one]
    rw [he] at hpow
    exact (S.smul_mem_iff hcoeff).mp hpow
  have hsingle (k : ℤ) (hk : k∈Set.Icc (0:ℤ) l) : Finsupp.single k (1:K)∈S := by
    have hklo := hk.1
    have hkhi := hk.2
    have hknat : (k.toNat:ℤ)=k := Int.toNat_of_nonneg hk.1
    have hfall : qFalling q l k.toNat≠0 := qFalling_ne_zero q l k.toNat (by omega) hq
    have hf := end_power_preserves S (quantumF q l) hF _ hhigh k.toNat
    rw [quantumF_power_single] at hf
    simp only [zero_add,sub_zero,one_mul,hknat] at hf
    have he : Finsupp.single k (qFalling q l k.toNat)=
        qFalling q l k.toNat • Finsupp.single k (1:K) := by
      simp only [Finsupp.smul_single,smul_eq_mul,mul_one]
    rw [he] at hf
    exact (S.smul_mem_iff hfall).mp hf
  apply le_antisymm hS
  intro v hv
  rw [← Finsupp.sum_single v,Finsupp.sum]
  apply Submodule.sum_mem
  intro k hk
  have hh := S.smul_mem (v k) (hsingle k (hv hk))
  simpa only [Finsupp.smul_single,smul_eq_mul,mul_one] using hh

end AMSPhysical

#print axioms AMSPhysical.quantumEF_irreducible
