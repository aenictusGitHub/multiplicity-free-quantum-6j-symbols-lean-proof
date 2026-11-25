import QuantumBinomialTheorem
import QuantumClebsch

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1400000
noncomputable section
namespace AMSPhysical
open Module
open scoped TensorProduct

def tensorQuantumF (q : ℝ) (l m : ℤ) : Module.End ℝ (WeightModule ℝ ⊗[ℝ] WeightModule ℝ) :=
  TensorProduct.map (quantumF q l) (1 : Module.End ℝ (WeightModule ℝ))+TensorProduct.map (quantumKinv q l) (quantumF q m)

theorem quantumKinv_F (q : ℝ) (hq : q≠0) (l : ℤ) :
    quantumKinv q l*quantumF q l=q^2 • (quantumF q l*quantumKinv q l) := by
  apply Finsupp.lhom_ext
  intro k a
  simp only [Module.End.mul_apply,quantumKinv,quantumF,weightShift_single,add_zero,
    LinearMap.smul_apply,Finsupp.smul_single,smul_eq_mul]
  have he : -(l-2*(k+1))=2+(-(l-2*k)) := by omega
  rw [he,zpow_add₀ hq]
  simp only [zpow_ofNat]
  apply congrArg (Finsupp.single (k+1))
  ring

theorem tensorQuantumF_qcommute (q : ℝ) (hq : q≠0) (l m : ℤ) :
    TensorProduct.map (quantumKinv q l) (quantumF q m)*TensorProduct.map (quantumF q l) (1 : Module.End ℝ (WeightModule ℝ))=
      q^2 • (TensorProduct.map (quantumF q l) (1 : Module.End ℝ (WeightModule ℝ))*TensorProduct.map (quantumKinv q l) (quantumF q m)) := by
  rw [← TensorProduct.map_mul,← TensorProduct.map_mul,mul_one,one_mul,quantumKinv_F q hq l,
    TensorProduct.map_smul_left]

theorem quantumKinv_power_single (q : ℝ) (hq : q≠0) (l k : ℤ) (a : ℝ) (n : ℕ) :
    ((quantumKinv q l)^n) (Finsupp.single k a)=
      Finsupp.single k (a*q^(-(n:ℤ)*(l-2*k))) := by
  induction n with
  | zero => simp only [pow_zero,Module.End.one_apply,Nat.cast_zero,neg_zero,zero_mul,zpow_zero,mul_one]
  | succ n ih =>
    rw [pow_succ',Module.End.mul_apply,ih]
    simp only [quantumKinv,weightShift_single,add_zero]
    have he : -((n+1:ℕ):ℤ)*(l-2*k)=-(n:ℤ)*(l-2*k)+(-(l-2*k)) := by push_cast;ring
    rw [he,zpow_add₀ hq,mul_assoc]

theorem tensorQuantumF_monomial (q : ℝ) (hq : q≠0) (l m k j : ℤ) (a b : ℕ) :
    ((TensorProduct.map (quantumF q l) (1 : Module.End ℝ (WeightModule ℝ)))^a*(TensorProduct.map (quantumKinv q l) (quantumF q m))^b)
      (tensorWeightBasis k j)=
      (q^(-(b:ℤ)*(l-2*k))*qFalling q (l-k) a*qFalling q (m-j) b) •
        tensorWeightBasis (k+(a:ℤ)) (j+(b:ℤ)) := by
  simp only [Module.End.mul_apply,TensorProduct.map_pow,one_pow,tensorWeightBasis,
    TensorProduct.map_tmul,Module.End.one_apply,quantumKinv_power_single q hq,
    quantumF_power_single,one_mul]
  rw [single_tensor_single]
  simp only [tensorWeightBasis]

theorem tensorQuantumF_power_basis (q : ℝ) (hq : q≠0) (l m k j : ℤ) (a : ℕ) :
    ((tensorQuantumF q l m)^a) (tensorWeightBasis k j)=
      ∑ t∈Finset.range (a+1),
        (gaussianBinomial (q^2) a t*q^(-(t:ℤ)*(l-2*k))*qFalling q (l-k) (a-t)*qFalling q (m-j) t) •
          tensorWeightBasis (k+((a-t:ℕ):ℤ)) (j+(t:ℤ)) := by
  have he := qcommute_add_pow (q^2) (TensorProduct.map (quantumF q l) (1 : Module.End ℝ (WeightModule ℝ)))
    (TensorProduct.map (quantumKinv q l) (quantumF q m)) (tensorQuantumF_qcommute q hq l m) a
  have hv := congrArg (fun T : Module.End ℝ (WeightModule ℝ ⊗[ℝ] WeightModule ℝ) => T (tensorWeightBasis k j)) he
  dsimp only at hv
  change ((tensorQuantumF q l m)^a) (tensorWeightBasis k j)=_ at hv
  rw [hv]
  simp only [LinearMap.sum_apply,LinearMap.smul_apply,tensorQuantumF_monomial q hq,smul_smul]
  apply Finset.sum_congr rfl
  intro t ht
  congr 1
  ring

end AMSPhysical

#print axioms AMSPhysical.tensorQuantumF_power_basis
