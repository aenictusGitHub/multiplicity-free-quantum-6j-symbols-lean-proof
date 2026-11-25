import QuantumPairHomogeneous
import GradedOscillatorPowers
import QuantumOscillatorLadderScalar
import OccupationTensorCoefficients

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem occupationTensorCoefficients_homogeneous (n l m : ℕ)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) :
    CoefficientHomogeneous (occupationPairDegree n) ((l:ℤ)+(m:ℤ)) (occupationTensorCoefficients n l m v) := by
  intro p hp
  obtain ⟨hx,hy⟩:=occupationTensorCoefficients_support n l m v p.1 p.2 hp
  change (∑ i : Fin (n+1),p.1 i)+(∑ i : Fin (n+1),p.2 i)=(l:ℤ)+(m:ℤ)
  rw [hx.2,hy.2]

/-- Closed, all-rank annihilation-through-cup-power formula on the actual
occupation operators. No nonzero ladder coefficient is required. -/
theorem pairLatticeAnnihilation_creation_power (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (n : ℕ) (a : ℤ) (f : OccupationPairLattice n →₀ ℝ)
    (hf : CoefficientHomogeneous (occupationPairDegree n) a f) (t : ℕ) :
    pairLatticeAnnihilation q n (((pairLatticeCreation q n)^(t+1)) f)=
      (q^(-2:ℤ))^(t+1) • ((pairLatticeCreation q n)^(t+1)) (pairLatticeAnnihilation q n f)+
        quantumOscillatorLadderCoefficient q (a+(n:ℤ)) (t+1) • ((pairLatticeCreation q n)^t) f := by
  apply gradedOscillator_power (pairLatticeCreation q n) (pairLatticeAnnihilation q n) (q^(-2:ℤ))
    (quantumOscillatorLadderCoefficient q (a+(n:ℤ)))
    (fun s =>q^(-(a+(n:ℤ))-2*(s:ℤ))*qInteger q (a+(n:ℤ)+2*(s:ℤ)+1))
    (quantumOscillatorLadderCoefficient_zero q (a+(n:ℤ)))
    (quantumOscillatorLadderCoefficient_succ q hq hD (a+(n:ℤ))) f
  intro s
  have h:=pairLatticeAnnihilation_creation_homogeneous q hq hD n (a+2*(s:ℤ))
    (((pairLatticeCreation q n)^s) f) (pairLatticeCreation_pow_homogeneous q n a f hf s)
  have he : -(a+2*(s:ℤ))-(n:ℤ)= -(a+(n:ℤ))-2*(s:ℤ) := by ring
  have he' : a+2*(s:ℤ)+(n:ℤ)+1=a+(n:ℤ)+2*(s:ℤ)+1 := by ring
  rw [he,he'] at h
  simpa only [pow_succ',Module.End.mul_apply] using h

end AMSPhysical
#print axioms AMSPhysical.pairLatticeAnnihilation_creation_power
