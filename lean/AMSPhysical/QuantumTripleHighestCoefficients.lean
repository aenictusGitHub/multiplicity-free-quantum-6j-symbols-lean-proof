import QuantumTripleCreationIntertwiner
import QuantumTripleHighestBase
import QuantumTripleCupBase

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical

def PhysicalTripleHighestCoefficients (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n l m c : ℕ)
    (f : OccupationTripleLattice n →₀ ℝ) (lam : Fin n → ℤ) : Prop :=
  ∃ v : quantumOccupationTripleSpace n l m c,occupationTripleCoefficients n l m c v=f ∧
    (∀ i : Fin n,typeAMixedTriple q hq hD n l m c (typeAAlgebraGenerator q n i 0) v=0) ∧
    (∀ i : Fin n,typeAMixedTriple q hq hD n l m c (typeAAlgebraGenerator q n i 2) v=q^(lam i) • v)

theorem physicalTripleHighestCoefficients_left_creation (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (n l m c : ℕ) (f : OccupationTripleLattice n →₀ ℝ) (lam : Fin n → ℤ)
    (hf : PhysicalTripleHighestCoefficients q hq hD n l m c f lam) :
    PhysicalTripleHighestCoefficients q hq hD n (l+1) (m+1) c (tripleLeftCreation q n f) lam := by
  obtain ⟨v,hcoef,hE,hK⟩:=hf
  refine ⟨finiteTripleLeftCreation q n l m c v,?_,?_,?_⟩
  · rw [occupationTripleCoefficients_leftCreation,hcoef]
  · intro i
    rw [← finiteTripleLeftCreation_intertwines q hq hD,hE,map_zero]
  · intro i
    rw [← finiteTripleLeftCreation_intertwines q hq hD,hK,map_smul]

theorem physicalTripleHighestCoefficients_right_creation (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (n l m c : ℕ) (f : OccupationTripleLattice n →₀ ℝ) (lam : Fin n → ℤ)
    (hf : PhysicalTripleHighestCoefficients q hq hD n l m c f lam) :
    PhysicalTripleHighestCoefficients q hq hD n l (m+1) (c+1) (tripleRightCreation q n f) lam := by
  obtain ⟨v,hcoef,hE,hK⟩:=hf
  refine ⟨finiteTripleRightCreation q n l m c v,?_,?_,?_⟩
  · rw [occupationTripleCoefficients_rightCreation,hcoef]
  · intro i
    rw [← finiteTripleRightCreation_intertwines q hq hD,hE,map_zero]
  · intro i
    rw [← finiteTripleRightCreation_intertwines q hq hD,hK,map_smul]

theorem physicalTripleHighestCoefficients_base (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n a h b : ℕ) :
    PhysicalTripleHighestCoefficients q hq hD n a h b (tripleCupBase n (a:ℤ) (h:ℤ) (b:ℤ))
      (mixedHighestDynkin n (a+b) h) := by
  refine ⟨physicalTripleHighestBase n a h b,?_,physicalTripleHighestBase_E q hq hD n a h b,
    physicalTripleHighestBase_K q hq hD n a h b⟩
  unfold physicalTripleHighestBase
  rw [occupationTripleCoefficients_basis]
  rfl

theorem physicalTripleHighestCoefficients_right_power (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (n a h b k : ℕ) :
    PhysicalTripleHighestCoefficients q hq hD n a (h+k) (b+k)
      (((tripleRightCreation q n)^k) (tripleCupBase n (a:ℤ) (h:ℤ) (b:ℤ))) (mixedHighestDynkin n (a+b) h) := by
  induction k with
  | zero => simpa only [Nat.add_zero,pow_zero,Module.End.one_apply] using physicalTripleHighestCoefficients_base q hq hD n a h b
  | succ k ih =>
    have h0:=physicalTripleHighestCoefficients_right_creation q hq hD n a (h+k) (b+k) _ _ ih
    simpa only [Nat.add_assoc,pow_succ',Module.End.mul_apply] using h0

/-- Concrete cup powers are highest vectors for the FULL independently
presented quantum triple action. Both finite physical support and full-algebra
creation intertwinings are used, not a candidate recoupling formula. -/
theorem physicalTripleHighestCoefficients_cup_power (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (n a h b t k : ℕ) :
    PhysicalTripleHighestCoefficients q hq hD n (a+t) (h+k+t) (b+k)
      (((tripleLeftCreation q n)^t) (((tripleRightCreation q n)^k) (tripleCupBase n (a:ℤ) (h:ℤ) (b:ℤ))))
      (mixedHighestDynkin n (a+b) h) := by
  induction t with
  | zero => simpa only [Nat.add_zero,pow_zero,Module.End.one_apply] using physicalTripleHighestCoefficients_right_power q hq hD n a h b k
  | succ t ih =>
    have h0:=physicalTripleHighestCoefficients_left_creation q hq hD n (a+t) (h+k+t) (b+k) _ _ ih
    simpa only [Nat.add_assoc,pow_succ',Module.End.mul_apply] using h0

end AMSPhysical
#print axioms AMSPhysical.physicalTripleHighestCoefficients_cup_power
