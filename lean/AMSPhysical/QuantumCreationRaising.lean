import QuantumCreationRaisingScalar
import WeightedTranslationAlgebra

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

theorem weightedTranslation_add {X : Type*} [AddCommGroup X] (s : X) (w v : X → ℝ) :
    weightedTranslation s w+weightedTranslation s v=weightedTranslation s (fun x =>w x+v x) := by
  apply Finsupp.lhom_ext
  intro x a
  simp only [LinearMap.add_apply,weightedTranslation_single,← Finsupp.single_add]
  congr 1
  ring

theorem mixedCreation_first_commutator (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (n : ℕ) (i : Fin n) (k : Fin (n+1)) :
    weightedTranslation (mixedCreationShift n k) (mixedCreationCoefficient q n k)*
        weightedTranslation (latticeRoot i.castSucc i.succ,0) (pairRaisingFirstWeight q n i)-
      weightedTranslation (latticeRoot i.castSucc i.succ,0) (pairRaisingFirstWeight q n i)*
        weightedTranslation (mixedCreationShift n k) (mixedCreationCoefficient q n k)=
      if k=i.succ then weightedTranslation (mixedCreationShift n k+(latticeRoot i.castSucc i.succ,0))
        (fun p => -mixedCreationCoefficient q n k p*q^(p.1 i.succ+1-simpleOccupationWeight n p.2 i)) else 0 := by
  rw [weightedTranslation_commutator]
  simp_rw [mixedCreation_raising_first_coefficient q hq hD]
  split_ifs <;> simp only [weightedTranslation_zero]

theorem mixedCreation_second_commutator (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (n : ℕ) (i : Fin n) (k : Fin (n+1)) :
    weightedTranslation (mixedCreationShift n k) (mixedCreationCoefficient q n k)*
        weightedTranslation (0,-latticeRoot i.castSucc i.succ) (pairRaisingSecondWeight q n i)-
      weightedTranslation (0,-latticeRoot i.castSucc i.succ) (pairRaisingSecondWeight q n i)*
        weightedTranslation (mixedCreationShift n k) (mixedCreationCoefficient q n k)=
      if k=i.castSucc then weightedTranslation (mixedCreationShift n k+(0,-latticeRoot i.castSucc i.succ))
        (fun p => -mixedCreationCoefficient q n k p*q^(-p.2 i.castSucc)) else 0 := by
  rw [weightedTranslation_commutator]
  simp_rw [mixedCreation_raising_second_coefficient q hq hD]
  split_ifs <;> simp only [weightedTranslation_zero]

theorem mixedCreation_crossing_shift (n : ℕ) (i : Fin n) :
    mixedCreationShift n i.succ+(latticeRoot i.castSucc i.succ,0)=
      mixedCreationShift n i.castSucc+(0,-latticeRoot i.castSucc i.succ) := by
  ext k <;> simp [mixedCreationShift,latticeRoot,Pi.single_apply]

theorem mixedCreation_crossing_cancel (q : ℝ) (hq : q≠0) (n : ℕ) (i : Fin n)
    (p : OccupationPairLattice n) :
    -mixedCreationCoefficient q n i.succ p*q^(p.1 i.succ+1-simpleOccupationWeight n p.2 i)+
      -mixedCreationCoefficient q n i.castSucc p*q^(-p.2 i.castSucc)=0 := by
  have he : p.1 i.succ+1-simpleOccupationWeight n p.2 i=
      (p.1 i.succ+p.2 i.succ+1)+(-p.2 i.castSucc) := by unfold simpleOccupationWeight;ring
  rw [he,zpow_add₀ hq]
  linear_combination -q^(-p.2 i.castSucc)*mixedCreationCoefficient_adjacent q hq n i p

/-- Direct occupation-lattice verification of the creation intertwiner against
every raising generator, with both crossing terms retained and cancelled. -/
theorem pairLatticeCreation_commutes_raising (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (n : ℕ) (i : Fin n) :
    pairLatticeCreation q n*pairLatticeRaising q n i=
      pairLatticeRaising q n i*pairLatticeCreation q n := by
  classical
  apply sub_eq_zero.mp
  change (∑ k : Fin (n+1),weightedTranslation (mixedCreationShift n k) (mixedCreationCoefficient q n k))*
      (weightedTranslation (latticeRoot i.castSucc i.succ,0) (pairRaisingFirstWeight q n i)+
        weightedTranslation (0,-latticeRoot i.castSucc i.succ) (pairRaisingSecondWeight q n i))-
      (weightedTranslation (latticeRoot i.castSucc i.succ,0) (pairRaisingFirstWeight q n i)+
        weightedTranslation (0,-latticeRoot i.castSucc i.succ) (pairRaisingSecondWeight q n i))*
      (∑ k : Fin (n+1),weightedTranslation (mixedCreationShift n k) (mixedCreationCoefficient q n k))=0
  rw [Finset.sum_mul,Finset.mul_sum,← Finset.sum_sub_distrib]
  have hs : ∀ k : Fin (n+1),
      weightedTranslation (mixedCreationShift n k) (mixedCreationCoefficient q n k)*
          (weightedTranslation (latticeRoot i.castSucc i.succ,0) (pairRaisingFirstWeight q n i)+
            weightedTranslation (0,-latticeRoot i.castSucc i.succ) (pairRaisingSecondWeight q n i))-
        (weightedTranslation (latticeRoot i.castSucc i.succ,0) (pairRaisingFirstWeight q n i)+
            weightedTranslation (0,-latticeRoot i.castSucc i.succ) (pairRaisingSecondWeight q n i))*
          weightedTranslation (mixedCreationShift n k) (mixedCreationCoefficient q n k)=
      (if k=i.succ then weightedTranslation (mixedCreationShift n k+(latticeRoot i.castSucc i.succ,0))
        (fun p => -mixedCreationCoefficient q n k p*q^(p.1 i.succ+1-simpleOccupationWeight n p.2 i)) else 0)+
      (if k=i.castSucc then weightedTranslation (mixedCreationShift n k+(0,-latticeRoot i.castSucc i.succ))
        (fun p => -mixedCreationCoefficient q n k p*q^(-p.2 i.castSucc)) else 0) := by
    intro k
    rw [← mixedCreation_first_commutator q hq hD,← mixedCreation_second_commutator q hq hD]
    noncomm_ring
  simp_rw [hs]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [mixedCreation_crossing_shift,weightedTranslation_add]
  simp_rw [mixedCreation_crossing_cancel q hq]
  exact weightedTranslation_zero _

end AMSPhysical
#print axioms AMSPhysical.pairLatticeCreation_commutes_raising
