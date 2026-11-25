import QuantumMixedWeightPairs
import QuantumMixedUnique
import BasisSupportedInjection
import JointEigenCoordinates

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 4200000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem typeAMixedTensor_K_basis (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n l m : ℕ)
    (i : Fin n) (p : occupationWeights (Fin (n+1)) l × occupationWeights (Fin (n+1)) m) :
    typeAMixedTensor q hq hD n l m (typeAAlgebraGenerator q n i 2)
      (((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l).tensorProduct
        (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m)) p)=
      q^(simpleOccupationWeight n p.1.val i-simpleOccupationWeight n p.2.val i) •
      (((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l).tensorProduct
        (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m)) p) := by
  simp only [Module.Basis.tensorProduct_apply']
  have he : typeAMixedTensor q hq hD n l m (typeAAlgebraGenerator q n i 2)
      (quantumOccupationBasis (K:=ℝ) l p.1 ⊗ₜ[ℝ] quantumOccupationBasis (K:=ℝ) m p.2)=
      typeAFiniteGenerator q hq hD n l i 2 (quantumOccupationBasis (K:=ℝ) l p.1) ⊗ₜ[ℝ]
      typeAFiniteGenerator q hq hD n m i 3 (quantumOccupationBasis (K:=ℝ) m p.2) := by
    simp [typeAMixedTensor,typeATensorRepresentation,typeAQuantumCoproduct_generator,typeACoproductK,
      typeAOpposite_generator,Module.endTensorEndAlgHom_apply,
      TensorProduct.AlgebraTensorModule.map_tmul,typeAFiniteGenerator]
  rw [he,typeAFiniteGenerator_K_basis,typeAFiniteGenerator_Ki_basis]
  simp only [← TensorProduct.smul_tmul',TensorProduct.tmul_smul,smul_smul]
  rw [← zpow_add₀ hq]
  congr 1
  ring

/-- Every vector of the required ACTUAL joint Cartan weight lies in the
explicit contracted tensor weight space. This closes the previous support gap. -/
theorem mixedTensor_weight_reconstruction (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n r a b : ℕ) (hn : 0<n)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) (r+a) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (r+b))
    (hK : ∀ i : Fin n,typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      n (r+a) (r+b) (typeAAlgebraGenerator q n i 2) v=q^(mixedHighestDynkin n a b i) • v) :
    ∃ f : occupationWeights (Fin (n+1)) r → ℝ,v=mixedTensorSum n r a b f := by
  classical
  let B := (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) (r+a)).tensorProduct
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) (r+b))
  let e : occupationWeights (Fin (n+1)) r →
      occupationWeights (Fin (n+1)) (r+a) × occupationWeights (Fin (n+1)) (r+b) :=
    fun t => (shiftedOccupation n r a 0 t,shiftedOccupation n r b (Fin.last n) t)
  have he : Function.Injective e := by intro x y h;exact shiftedOccupation_injective n r a 0 (congrArg Prod.fst h)
  have hs : ∀ p,B.repr v p≠0 → ∃ t,e t=p := by
    intro p hp
    have hw : ∀ i : Fin n,simpleOccupationWeight n p.1.val i-simpleOccupationWeight n p.2.val i=mixedHighestDynkin n a b i := by
      intro i
      have hdiag : ∀ xy : occupationWeights (Fin (n+1)) (r+a) × occupationWeights (Fin (n+1)) (r+b),
          typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
            n (r+a) (r+b) (typeAAlgebraGenerator q n i 2) (B xy)=
            q^(simpleOccupationWeight n xy.1.val i-simpleOccupationWeight n xy.2.val i) • B xy := by
        intro xy
        exact typeAMixedTensor_K_basis q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n (r+a) (r+b) i xy
      have hz := eigenbasis_repr (K:=ℝ)
        (V:=quantumOccupationSpace ℝ (Fin (n+1)) (r+a) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (r+b))
        (ι:=occupationWeights (Fin (n+1)) (r+a) × occupationWeights (Fin (n+1)) (r+b))
        B (typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
          n (r+a) (r+b) (typeAAlgebraGenerator q n i 2))
        (fun xy => q^(simpleOccupationWeight n xy.1.val i-simpleOccupationWeight n xy.2.val i)) hdiag v p
      rw [hK i,map_smul,Finsupp.smul_apply,smul_eq_mul] at hz
      exact zpow_right_injective₀ hq hq1 (mul_right_cancel₀ hp hz.symm)

    obtain ⟨t,hx,hy⟩ := mixedWeight_pair_reconstruction n r a b hn p.1 p.2 hw
    exact ⟨t,Prod.ext hx hy⟩
  refine ⟨fun t => B.repr v (e t),?_⟩
  conv_lhs => rw [basis_sum_of_supported_injection B e he v hs]
  unfold mixedTensorSum
  apply Finset.sum_congr rfl
  intro t ht
  rw [Module.Basis.tensorProduct_apply']
  rfl

/-- Full physical mixed highest-weight multiplicity one: every vector with
this actual Cartan weight annihilated by every simple E is on the constructed
highest line, with no assumed support or representation decomposition. -/
theorem mixedHighest_full_weight_unique (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n r a b : ℕ) (hn : 0<n)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) (r+a) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (r+b))
    (hK : ∀ i : Fin n,typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      n (r+a) (r+b) (typeAAlgebraGenerator q n i 2) v=q^(mixedHighestDynkin n a b i) • v)
    (hE : ∀ i : Fin n,typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      n (r+a) (r+b) (typeAAlgebraGenerator q n i 0) v=0) :
    ∃ s : ℝ,v=s • mixedHighestVector q n r a b := by
  obtain ⟨f,hf⟩ := mixedTensor_weight_reconstruction q hq hq1 n r a b hn v hK
  have hEf : ∀ i : Fin n,typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      n (r+a) (r+b) (typeAAlgebraGenerator q n i 0) (mixedTensorSum n r a b f)=0 := by
    intro i
    rw [← hf]
    exact hE i
  refine ⟨f (highestOccupation n r)/mixedHighestCoefficient q n r b (highestOccupation n r),?_⟩
  rw [hf]
  exact mixedTensorSum_highest_unique q hq hq1 n r a b f hEf

end AMSPhysical
#print axioms AMSPhysical.mixedHighest_full_weight_unique
