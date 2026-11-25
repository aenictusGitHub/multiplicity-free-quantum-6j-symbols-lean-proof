import QuantumTypeAMixedTriple
import QuantumMixedWeight

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def physicalTripleHighestBase (n a h b : ℕ) : quantumOccupationTripleSpace n a h b :=
  occupationTripleBasis n a h b (highestOccupation n a,lowestOccupation n h,highestOccupation n b)

theorem simpleOccupationWeight_highest (n a : ℕ) (i : Fin n) :
    simpleOccupationWeight n (highestOccupation n a).val i=(a:ℤ)*(if i.castSucc=0 then 1 else 0) := by
  unfold simpleOccupationWeight
  rw [highestOccupation_source_zero]
  simp only [highestOccupation,Pi.single_apply,sub_zero]
  by_cases hi : i.castSucc=0 <;> simp [hi,eq_comm]

theorem simpleOccupationWeight_lowest (n h : ℕ) (i : Fin n) :
    simpleOccupationWeight n (lowestOccupation n h).val i= -(h:ℤ)*(if i.succ=Fin.last n then 1 else 0) := by
  unfold simpleOccupationWeight
  rw [lowestOccupation_source_zero]
  simp only [lowestOccupation,Pi.single_apply,zero_sub]
  by_cases hi : i.succ=Fin.last n <;> simp [hi,eq_comm]

theorem physicalTripleHighestBase_E (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n a h b : ℕ) (i : Fin n) :
    typeAMixedTriple q hq hD n a h b (typeAAlgebraGenerator q n i 0) (physicalTripleHighestBase n a h b)=0 := by
  unfold physicalTripleHighestBase
  rw [occupationTripleBasis_apply]
  unfold typeAMixedTriple typeAReverseMixedTensor
  have hx : typeAFiniteQuantumRepresentation q hq hD n a (typeAAlgebraGenerator q n i 0)
      (quantumOccupationBasis (K:=ℝ) a (highestOccupation n a))=0 := typeAFiniteGenerator_highest_E q hq hD n a i
  have hz : typeAFiniteQuantumRepresentation q hq hD n b (typeAAlgebraGenerator q n i 0)
      (quantumOccupationBasis (K:=ℝ) b (highestOccupation n b))=0 := typeAFiniteGenerator_highest_E q hq hD n b i
  rw [typeATensorRepresentation_E,hx,TensorProduct.zero_tmul,zero_add,typeATensorRepresentation_E,
    typeAOpposite_highest_E q hq hD,hz]
  simp

theorem typeAMixedTriple_K_basis (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n l m c : ℕ)
    (p : OccupationTripleIndex n l m c) (i : Fin n) :
    typeAMixedTriple q hq hD n l m c (typeAAlgebraGenerator q n i 2) (occupationTripleBasis n l m c p)=
      q^(simpleOccupationWeight n p.1.val i-simpleOccupationWeight n p.2.1.val i+simpleOccupationWeight n p.2.2.val i) •
        occupationTripleBasis n l m c p := by
  rw [occupationTripleBasis_apply]
  unfold typeAMixedTriple typeAReverseMixedTensor
  have hx : typeAFiniteQuantumRepresentation q hq hD n l (typeAAlgebraGenerator q n i 2)
      (quantumOccupationBasis (K:=ℝ) l p.1)=q^(simpleOccupationWeight n p.1.val i) • quantumOccupationBasis (K:=ℝ) l p.1 :=
    typeAFiniteGenerator_K_basis q hq hD n l i p.1
  have hz : typeAFiniteQuantumRepresentation q hq hD n c (typeAAlgebraGenerator q n i 2)
      (quantumOccupationBasis (K:=ℝ) c p.2.2)=q^(simpleOccupationWeight n p.2.2.val i) • quantumOccupationBasis (K:=ℝ) c p.2.2 :=
    typeAFiniteGenerator_K_basis q hq hD n c i p.2.2
  have hy : typeAOppositeSymmetricRepresentation q hq hD n m (typeAAlgebraGenerator q n i 2)
      (quantumOccupationBasis (K:=ℝ) m p.2.1)=q^(-simpleOccupationWeight n p.2.1.val i) • quantumOccupationBasis (K:=ℝ) m p.2.1 := by
    rw [typeAOpposite_generator]
    exact typeAFiniteGenerator_Ki_basis q hq hD n m i p.2.1
  rw [typeATensorRepresentation_K,typeATensorRepresentation_K,hx,hy,hz,
    TensorProduct.smul_tmul_smul,TensorProduct.smul_tmul_smul]
  rw [← zpow_add₀ hq,← zpow_add₀ hq]
  congr 1
  congr 1
  ring

theorem physicalTripleHighestBase_K (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n a h b : ℕ) (i : Fin n) :
    typeAMixedTriple q hq hD n a h b (typeAAlgebraGenerator q n i 2) (physicalTripleHighestBase n a h b)=
      q^(mixedHighestDynkin n (a+b) h i) • physicalTripleHighestBase n a h b := by
  unfold physicalTripleHighestBase
  rw [typeAMixedTriple_K_basis,simpleOccupationWeight_highest,simpleOccupationWeight_lowest,simpleOccupationWeight_highest]
  have he : (a:ℤ)*(if i.castSucc=0 then 1 else 0)-(-(h:ℤ)*(if i.succ=Fin.last n then 1 else 0))+
      (b:ℤ)*(if i.castSucc=0 then 1 else 0)=mixedHighestDynkin n (a+b) h i := by
    unfold mixedHighestDynkin
    push_cast
    ring
  rw [he]

end AMSPhysical
