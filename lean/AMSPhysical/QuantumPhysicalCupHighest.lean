import QuantumTripleHighestCoefficients
import QuantumPhysicalCupVectors

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical

theorem physicalQuantumCupVector_highest_coefficients (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (n l m h c : ℕ) (r : QuantumCupIndex l m c) :
    PhysicalTripleHighestCoefficients q hq hD n l (m+h) c (quantumCupMonomialAt q n l m h c r)
      (mixedHighestDynkin n (l+c-m) h) := by
  let t:=r.val.val
  let k:=m-t
  let a:=l-t
  let b:=c-k
  have htl : t ≤ l := r.property.1
  have hkc : k ≤ c := r.property.2
  have htm : t ≤ m := by have hr:=r.val.isLt;dsimp only [t];omega
  have h0:=physicalTripleHighestCoefficients_cup_power q hq hD n a h b t k
  have he1 : a+t=l := by dsimp only [a];omega
  have he2 : h+k+t=m+h := by dsimp only [k];omega
  have he3 : b+k=c := by dsimp only [b];omega
  have he4 : a+b=l+c-m := by dsimp only [a,b,k];omega
  rw [he1,he2,he3,he4] at h0
  have hA : (a:ℤ)=(l:ℤ)-(t:ℤ) := by dsimp only [a];rw [Nat.cast_sub htl]
  have hB : (b:ℤ)=(c:ℤ)-(k:ℤ) := by dsimp only [b];rw [Nat.cast_sub hkc]
  rw [hA,hB] at h0
  exact h0

theorem physicalTripleHighestCoefficients_synthesis (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (n l m c : ℕ) (f : OccupationTripleLattice n →₀ ℝ) (lam : Fin n → ℤ)
    (hf : PhysicalTripleHighestCoefficients q hq hD n l m c f lam) :
    (∀ i : Fin n,typeAMixedTriple q hq hD n l m c (typeAAlgebraGenerator q n i 0) (occupationTripleSynthesis n l m c f)=0) ∧
    (∀ i : Fin n,typeAMixedTriple q hq hD n l m c (typeAAlgebraGenerator q n i 2) (occupationTripleSynthesis n l m c f)=
      q^(lam i) • occupationTripleSynthesis n l m c f) := by
  obtain ⟨v,hcoef,hE,hK⟩:=hf
  rw [← hcoef,occupationTripleSynthesis_coefficients]
  exact ⟨hE,hK⟩

theorem physicalQuantumCupVector_E (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (n l m h c : ℕ) (r : QuantumCupIndex l m c) (i : Fin n) :
    typeAMixedTriple q hq hD n l (m+h) c (typeAAlgebraGenerator q n i 0) (physicalQuantumCupVector q n l m h c r)=0 :=
  (physicalTripleHighestCoefficients_synthesis q hq hD n l (m+h) c _ _
    (physicalQuantumCupVector_highest_coefficients q hq hD n l m h c r)).1 i

theorem physicalQuantumCupVector_K (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (n l m h c : ℕ) (r : QuantumCupIndex l m c) (i : Fin n) :
    typeAMixedTriple q hq hD n l (m+h) c (typeAAlgebraGenerator q n i 2) (physicalQuantumCupVector q n l m h c r)=
      q^(mixedHighestDynkin n (l+c-m) h i) • physicalQuantumCupVector q n l m h c r :=
  (physicalTripleHighestCoefficients_synthesis q hq hD n l (m+h) c _ _
    (physicalQuantumCupVector_highest_coefficients q hq hD n l m h c r)).2 i

end AMSPhysical
#print axioms AMSPhysical.physicalQuantumCupVector_E
#print axioms AMSPhysical.physicalQuantumCupVector_K
