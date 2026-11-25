import QuantumClebschOrthogonality
import BilinearOrthonormal

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
noncomputable section
namespace AMSPhysical
open Module
open scoped TensorProduct

def orthonormalWeightVector (q : ℝ) (L : ℕ) (k : Fin (L+1)) : finiteWeightSpace (K:=ℝ) L :=
  (Real.sqrt (quantumWeight q L k.val))⁻¹ • standardWeightBasis L k

theorem orthonormalWeightVector_pair (q : ℝ) (hq : 0<q) (L : ℕ) (i j : Fin (L+1)) :
    quantumPair q L (orthonormalWeightVector q L i) (orthonormalWeightVector q L j)=
      if i=j then 1 else 0 := by
  unfold orthonormalWeightVector
  rw [quantumPair_smul_left,quantumPair_smul_right,quantumPair_basis]
  split_ifs with hij
  · subst j
    have hs := Real.sq_sqrt (quantumWeight_pos q hq L i.val).le
    have hn := ne_of_gt (Real.sqrt_pos.mpr (quantumWeight_pos q hq L i.val))
    field_simp
    exact hs.symm
  · simp only [mul_zero]

def orthonormalCoupledVector (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ) (p : CoupledIndex l m) :
    finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m :=
  unitaryQuantumClebschMap q hq hq1 l m p.1 (orthonormalWeightVector q (coupledLabel l m p.1) p.2)

theorem orthonormalCoupledVector_pair (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ)
    (p v : CoupledIndex l m) :
    quantumTensorBilin q l m (orthonormalCoupledVector q hq hq1 l m p)
      (orthonormalCoupledVector q hq hq1 l m v)=if p=v then 1 else 0 := by
  classical
  rcases p with ⟨r,i⟩
  rcases v with ⟨s,j⟩
  by_cases hrs : r=s
  · subst s
    unfold orthonormalCoupledVector
    rw [unitaryQuantumClebschMap_isometry,orthonormalWeightVector_pair q hq]
    congr 1
    exact propext ⟨fun h => by change i=j at h;subst j;rfl,fun h => eq_of_heq (Sigma.mk.inj h).2⟩
  · unfold orthonormalCoupledVector
    rw [unitaryQuantumClebschMap_orthogonal q hq hq1 l m r s hrs]
    rw [if_neg (fun h => hrs (Sigma.mk.inj h).1)]

def quantumOrthonormalCoupledBasis (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ) :
    Basis (CoupledIndex l m) ℝ (finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m) := by
  letI : Nonempty (CoupledIndex l m) := ⟨⟨0,0⟩⟩
  have hi : LinearIndependent ℝ (orthonormalCoupledVector q hq hq1 l m) :=
    bilinear_orthonormal_independent (V:=finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m)
      (quantumTensorBilin q l m) _ (orthonormalCoupledVector_pair q hq hq1 l m)
  exact basisOfLinearIndependentOfCardEqFinrank (K:=ℝ)
    (V:=finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m) hi (by
      rw [coupledIndex_card,Module.finrank_tensorProduct,finiteWeightSpace_finrank,finiteWeightSpace_finrank])

theorem quantumOrthonormalCoupledBasis_apply (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ)
    (p : CoupledIndex l m) :
    quantumOrthonormalCoupledBasis q hq hq1 l m p=orthonormalCoupledVector q hq hq1 l m p := by
  simp [quantumOrthonormalCoupledBasis]

end AMSPhysical

#print axioms AMSPhysical.quantumOrthonormalCoupledBasis
