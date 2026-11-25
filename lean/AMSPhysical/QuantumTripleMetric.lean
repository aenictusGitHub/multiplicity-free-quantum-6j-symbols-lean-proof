import QuantumTensorMetric
import TensorWeightedIsometries

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
noncomputable section
namespace AMSPhysical
open Module
open scoped TensorProduct

/-- These explicit specializations avoid repeated unfolding of supported Finsupp
subtypes when Lean resolves the group structure of an iterated tensor product. -/
instance realFiniteTensorAddCommGroup (l m : ℕ) :
    AddCommGroup (finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m) :=
  TensorProduct.addCommGroup

instance realFiniteTripleAddCommGroup (l m n : ℕ) :
    AddCommGroup ((finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m) ⊗[ℝ] finiteWeightSpace (K:=ℝ) n) :=
  TensorProduct.addCommGroup

def quantumTripleBilin (q : ℝ) (l m n : ℕ) :
    ((finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m) ⊗[ℝ] finiteWeightSpace (K:=ℝ) n) →ₗ[ℝ]
    ((finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m) ⊗[ℝ] finiteWeightSpace (K:=ℝ) n) →ₗ[ℝ] ℝ :=
  tensorWeightedBilin
    (V:=finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m)
    (W:=finiteWeightSpace (K:=ℝ) n) ((standardWeightBasis (K:=ℝ) l).tensorProduct (R:=ℝ) (standardWeightBasis (K:=ℝ) m))
    (standardWeightBasis (K:=ℝ) n)
    (fun ij : Fin (l+1) × Fin (m+1) => quantumWeight q l ij.1.val*quantumWeight q m ij.2.val) (fun k => quantumWeight q n k.val)

def quantumRightTripleBilin (q : ℝ) (l m n : ℕ) :
    (finiteWeightSpace (K:=ℝ) l ⊗[ℝ] (finiteWeightSpace (K:=ℝ) m ⊗[ℝ] finiteWeightSpace (K:=ℝ) n)) →ₗ[ℝ]
    (finiteWeightSpace (K:=ℝ) l ⊗[ℝ] (finiteWeightSpace (K:=ℝ) m ⊗[ℝ] finiteWeightSpace (K:=ℝ) n)) →ₗ[ℝ] ℝ :=
  tensorWeightedBilin
    (V:=finiteWeightSpace (K:=ℝ) l)
    (W:=finiteWeightSpace (K:=ℝ) m ⊗[ℝ] finiteWeightSpace (K:=ℝ) n) (standardWeightBasis (K:=ℝ) l)
    ((standardWeightBasis (K:=ℝ) m).tensorProduct (R:=ℝ) (standardWeightBasis (K:=ℝ) n))
    (fun i => quantumWeight q l i.val) (fun jk : Fin (m+1) × Fin (n+1) => quantumWeight q m jk.1.val*quantumWeight q n jk.2.val)

theorem quantumTriple_assoc_isometry (q : ℝ) (l m n : ℕ)
    (p v : (finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m) ⊗[ℝ] finiteWeightSpace (K:=ℝ) n) :
    quantumRightTripleBilin q l m n
      ((TensorProduct.assoc ℝ _ _ _) p) ((TensorProduct.assoc ℝ _ _ _) v)=quantumTripleBilin q l m n p v :=
  tensorWeightedBilin_assoc_isometry
    (V:=finiteWeightSpace (K:=ℝ) l) (W:=finiteWeightSpace (K:=ℝ) m) (U:=finiteWeightSpace (K:=ℝ) n)
    (standardWeightBasis (K:=ℝ) l)
    (standardWeightBasis (K:=ℝ) m) (standardWeightBasis (K:=ℝ) n)
    (fun i => quantumWeight q l i.val) (fun j => quantumWeight q m j.val)
    (fun k => quantumWeight q n k.val) p v

theorem quantumTriple_assoc_symm_isometry (q : ℝ) (l m n : ℕ)
    (p v : finiteWeightSpace (K:=ℝ) l ⊗[ℝ] (finiteWeightSpace (K:=ℝ) m ⊗[ℝ] finiteWeightSpace (K:=ℝ) n)) :
    quantumTripleBilin q l m n
      ((TensorProduct.assoc ℝ _ _ _).symm p) ((TensorProduct.assoc ℝ _ _ _).symm v)=quantumRightTripleBilin q l m n p v := by
  have h := quantumTriple_assoc_isometry q l m n
    ((TensorProduct.assoc ℝ _ _ _).symm p) ((TensorProduct.assoc ℝ _ _ _).symm v)
  rw [LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply] at h
  exact h.symm

theorem quantumTripleBilin_tmul (q : ℝ) (l m n : ℕ)
    (p p' : finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m)
    (v v' : finiteWeightSpace (K:=ℝ) n) :
    quantumTripleBilin q l m n (p ⊗ₜ[ℝ] v) (p' ⊗ₜ[ℝ] v')=
      quantumTensorBilin q l m p p'*quantumPair q n v v' := by
  unfold quantumTripleBilin
  rw [tensorWeightedBilin_tmul
    (V:=finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m)
    (W:=finiteWeightSpace (K:=ℝ) n)]
  unfold quantumTensorBilin tensorWeightedBilin finiteWeightedBilin quantumPair
  rfl

end AMSPhysical

#print axioms AMSPhysical.quantumTriple_assoc_isometry
