import QuantumPowers
import Mathlib.LinearAlgebra.TensorProduct.Basic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

variable {K : Type*} [Field K]

def tensorWeightBasis (k j : ℤ) : WeightModule K ⊗[K] WeightModule K :=
  Finsupp.single k 1 ⊗ₜ[K] Finsupp.single j 1

theorem single_tensor_single (k j : ℤ) (a b : K) :
    Finsupp.single k a ⊗ₜ[K] Finsupp.single j b=(a*b) • (tensorWeightBasis (K:=K) k j) := by
  simpa only [Finsupp.smul_single,smul_eq_mul,mul_one,tensorWeightBasis] using
    (TensorProduct.smul_tmul_smul a b (Finsupp.single k (1:K)) (Finsupp.single j (1:K)))

def tensorQuantumE (q : K) (m : ℤ) : Module.End K (WeightModule K ⊗[K] WeightModule K) :=
  TensorProduct.map (quantumE q) (quantumK q m)+TensorProduct.map 1 (quantumE q)

theorem tensorQuantumE_basis (q : K) (m k j : ℤ) :
    tensorQuantumE q m (tensorWeightBasis k j)=
      (qInteger q k*q^(m-2*j)) • tensorWeightBasis (k-1) j+
      qInteger q j • tensorWeightBasis k (j-1) := by
  simp only [tensorQuantumE,tensorWeightBasis,LinearMap.add_apply,TensorProduct.map_tmul,
    Module.End.one_apply,quantumE,quantumK,weightShift_single,one_mul,add_zero]
  rw [single_tensor_single,single_tensor_single]
  simp only [one_mul,sub_eq_add_neg,tensorWeightBasis]

def couplingCoefficient (q : K) (m : ℤ) (r : ℕ) : ℕ → K
  | 0 => 1
  | k+1 => -(couplingCoefficient q m r k*qInteger q ((r:ℤ)-k))/
      (qInteger q (k+1:ℕ)*q^(m-2*((r:ℤ)-k-1)))

theorem couplingCoefficient_step (q : K) (hq : q≠0) (m : ℤ) (r k : ℕ)
    (hk : qInteger q (k+1:ℕ)≠0) :
    couplingCoefficient q m r (k+1)*(qInteger q (k+1:ℕ)*q^(m-2*((r:ℤ)-k-1)))=
      -(couplingCoefficient q m r k*qInteger q ((r:ℤ)-k)) := by
  rw [couplingCoefficient,div_mul_cancel₀ _ (mul_ne_zero hk (zpow_ne_zero _ hq))]

/-- A highest-weight coupling vector obtained by solving the actual tensor E recurrence. -/
def coupledHighest (q : K) (m : ℤ) (r : ℕ) : WeightModule K ⊗[K] WeightModule K :=
  ∑ k∈Finset.range (r+1),couplingCoefficient q m r k • tensorWeightBasis (k:ℤ) ((r:ℤ)-k)

theorem coupledHighest_annihilated (q : K) (hq : q≠0) (m : ℤ) (r : ℕ)
    (hqi : ∀ k∈Finset.range r,qInteger q (k+1:ℕ)≠0) :
    tensorQuantumE q m (coupledHighest q m r)=0 := by
  classical
  let A (k : ℕ) : WeightModule K ⊗[K] WeightModule K :=
    (couplingCoefficient q m r k*qInteger q k*q^(m-2*((r:ℤ)-k))) •
      tensorWeightBasis ((k:ℤ)-1) ((r:ℤ)-k)
  let B (k : ℕ) : WeightModule K ⊗[K] WeightModule K :=
    (couplingCoefficient q m r k*qInteger q ((r:ℤ)-k)) •
      tensorWeightBasis (k:ℤ) ((r:ℤ)-k-1)
  have hA : A 0=0 := by simp only [A,Nat.cast_zero,qInteger_zero,mul_zero,zero_mul,zero_smul]
  have hB : B r=0 := by simp only [B,sub_self,qInteger_zero,mul_zero,zero_smul]
  have hstep (k : ℕ) (hk : k∈Finset.range r) : A (k+1)+B k=0 := by
    have hi : (k:ℤ)+1-1=(k:ℤ) := by omega
    have hj : (r:ℤ)-((k:ℤ)+1)=(r:ℤ)-k-1 := by omega
    have hh := couplingCoefficient_step q hq m r k (hqi k hk)
    simp only [Nat.cast_add,Nat.cast_one] at hh
    dsimp [A,B]
    rw [hi,hj,mul_assoc,hh]
    module
  have he (k : ℕ) : tensorQuantumE q m
      (couplingCoefficient q m r k • tensorWeightBasis (k:ℤ) ((r:ℤ)-k))=A k+B k := by
    rw [map_smul,tensorQuantumE_basis,smul_add,smul_smul,smul_smul]
    dsimp [A,B]
    congr 1
    rw [mul_assoc]
  unfold coupledHighest
  rw [map_sum]
  simp_rw [he]
  rw [Finset.sum_add_distrib,Finset.sum_range_succ' A,Finset.sum_range_succ B,hA,hB,add_zero,add_zero]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero hstep

def tensorQuantumK (q : K) (l m : ℤ) : Module.End K (WeightModule K ⊗[K] WeightModule K) :=
  TensorProduct.map (quantumK q l) (quantumK q m)

theorem tensorQuantumK_basis (q : K) (hq : q≠0) (l m k j : ℤ) :
    tensorQuantumK q l m (tensorWeightBasis k j)=
      q^(l+m-2*(k+j)) • tensorWeightBasis k j := by
  simp only [tensorQuantumK,tensorWeightBasis,TensorProduct.map_tmul,
    quantumK,weightShift_single,one_mul,add_zero]
  rw [single_tensor_single,← zpow_add₀ hq]
  congr 2
  ring

theorem coupledHighest_weight (q : K) (hq : q≠0) (l m : ℤ) (r : ℕ) :
    tensorQuantumK q l m (coupledHighest q m r)=q^(l+m-2*r) • coupledHighest q m r := by
  classical
  unfold coupledHighest
  rw [map_sum,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [map_smul,tensorQuantumK_basis q hq]
  have hi : (k:ℤ)+((r:ℤ)-k)=(r:ℤ) := by omega
  rw [hi,smul_smul,smul_smul,mul_comm]

def tensorCoefficient (k j : ℤ) : WeightModule K ⊗[K] WeightModule K →ₗ[K] K :=
  TensorProduct.lift ((LinearMap.mul K K).compl₁₂ (Finsupp.lapply k) (Finsupp.lapply j))

theorem tensorCoefficient_basis (k j a b : ℤ) :
    tensorCoefficient (K:=K) k j (tensorWeightBasis a b)=
      (if a=k then 1 else 0)*(if b=j then 1 else 0) := by
  classical
  simp [tensorCoefficient,tensorWeightBasis,Finsupp.single_apply]

theorem coupledHighest_coefficient (q : K) (m : ℤ) (r : ℕ) :
    tensorCoefficient (K:=K) 0 r (coupledHighest q m r)=1 := by
  classical
  unfold coupledHighest
  rw [map_sum]
  calc
    ∑ k∈Finset.range (r+1),tensorCoefficient (K:=K) 0 r
        (couplingCoefficient q m r k • tensorWeightBasis (k:ℤ) ((r:ℤ)-k))=
      tensorCoefficient (K:=K) 0 r (couplingCoefficient q m r 0 • tensorWeightBasis (0:ℤ) ((r:ℤ)-0)) := by
      apply Finset.sum_eq_single 0
      · intro k hk hk0
        have hi : (k:ℤ)≠0 := by omega
        simp only [map_smul,tensorCoefficient_basis,if_neg hi,zero_mul,smul_zero]
      · intro h0
        exact (h0 (Finset.mem_range.mpr (by omega))).elim
    _=1 := by simp [couplingCoefficient,tensorCoefficient_basis]

theorem coupledHighest_ne_zero (q : K) (m : ℤ) (r : ℕ) : coupledHighest q m r≠0 := by
  intro he
  have hh := coupledHighest_coefficient q m r
  rw [he,map_zero] at hh
  exact zero_ne_one hh

end AMSPhysical

#print axioms AMSPhysical.coupledHighest_annihilated
