import QuantumMixedTensor

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def mixedHighestDynkin (n a b : ℕ) (i : Fin n) : ℤ :=
  (a:ℤ)*(if i.castSucc=(0:Fin (n+1)) then 1 else 0)+
    (b:ℤ)*(if i.succ=Fin.last n then 1 else 0)

theorem shiftedOccupation_high_simpleWeight (n r a : ℕ)
    (x : occupationWeights (Fin (n+1)) r) (i : Fin n) :
    simpleOccupationWeight n (shiftedOccupation n r a 0 x).val i=
      simpleOccupationWeight n x.val i+(a:ℤ)*(if i.castSucc=(0:Fin (n+1)) then 1 else 0) := by
  unfold simpleOccupationWeight
  rw [shiftedOccupation_high_source]
  change (x.val i.castSucc+(Pi.single 0 (a:ℤ) : Fin (n+1) → ℤ) i.castSucc)-x.val i.succ=_
  simp only [Pi.single_apply]
  by_cases hi : i.castSucc=(0:Fin (n+1)) <;> simp [hi,eq_comm] <;> ring

theorem mixedOccupationTensor_K (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n r a b : ℕ)
    (i : Fin n) (t : occupationWeights (Fin (n+1)) r) :
    typeAMixedTensor q hq hD n (r+a) (r+b) (typeAAlgebraGenerator q n i 2) (mixedOccupationTensor n r a b t)=
      q^(mixedHighestDynkin n a b i) • mixedOccupationTensor n r a b t := by
  have he : typeAMixedTensor q hq hD n (r+a) (r+b) (typeAAlgebraGenerator q n i 2) (mixedOccupationTensor n r a b t)=
      typeAFiniteGenerator q hq hD n (r+a) i 2
        (quantumOccupationBasis (K:=ℝ) (r+a) (shiftedOccupation n r a 0 t)) ⊗ₜ[ℝ]
      typeAFiniteGenerator q hq hD n (r+b) i 3
        (quantumOccupationBasis (K:=ℝ) (r+b) (shiftedOccupation n r b (Fin.last n) t)) := by
    simp [typeAMixedTensor,mixedOccupationTensor,typeATensorRepresentation,typeAQuantumCoproduct_generator,
      typeACoproductK,typeAOpposite_generator,Module.endTensorEndAlgHom_apply,
      TensorProduct.AlgebraTensorModule.map_tmul,typeAFiniteGenerator]
  rw [he,typeAFiniteGenerator_K_basis,typeAFiniteGenerator_Ki_basis]
  simp only [← TensorProduct.smul_tmul',TensorProduct.tmul_smul,smul_smul]
  rw [← zpow_add₀ hq,shiftedOccupation_high_simpleWeight,shiftedOccupation_low_simpleWeight]
  have hpow : -(simpleOccupationWeight n t.val i-(b:ℤ)*(if i.succ=Fin.last n then 1 else 0))+
      (simpleOccupationWeight n t.val i+(a:ℤ)*(if i.castSucc=(0:Fin (n+1)) then 1 else 0))=
      mixedHighestDynkin n a b i := by unfold mixedHighestDynkin;ring
  rw [hpow]
  rfl

/-- The actual mixed tensor vector has the expected end-node highest weight
(r-independent): a omega_1 + b omega_n. -/
theorem mixedHighestVector_K (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n r a b : ℕ) (i : Fin n) :
    typeAMixedTensor q hq hD n (r+a) (r+b) (typeAAlgebraGenerator q n i 2) (mixedHighestVector q n r a b)=
      q^(mixedHighestDynkin n a b i) • mixedHighestVector q n r a b := by
  unfold mixedHighestVector
  simp only [map_sum,map_smul,mixedOccupationTensor_K,Finset.smul_sum,smul_smul]
  apply Finset.sum_congr rfl
  intro t ht
  congr 1
  ring

end AMSPhysical
#print axioms AMSPhysical.mixedHighestVector_K
