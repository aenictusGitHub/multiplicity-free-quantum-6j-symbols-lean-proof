import QuantumTripleCrossPower
import QuantumTripleLeftPowers

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical

/-- Concrete cup monomials in the unrestricted occupation coefficient space.
Physical nonnegative degrees will be imposed when constructing their basis. -/
def quantumCupMonomial (q : ℝ) (n : ℕ) (l h c : ℤ) (t k : ℕ) : OccupationTripleLattice n →₀ ℝ :=
  ((tripleLeftCreation q n)^t) (((tripleRightCreation q n)^k) (tripleCupBase n (l-(t:ℤ)) h (c-(k:ℤ))))

def quantumCupLeftDiagonal (q : ℝ) (n : ℕ) (l h : ℤ) (t k : ℕ) : ℝ :=
  q^(-l-h-(t:ℤ)-(k:ℤ)-(n:ℤ)+2)*qInteger q (t:ℤ)*qInteger q (l+h+(k:ℤ)+(n:ℤ))

def quantumCupLeftOffDiagonal (q : ℝ) (n : ℕ) (l h c : ℤ) (t k : ℕ) : ℝ :=
  (-1:ℝ)^n*q^(1-(n:ℤ)-h-c-2*(t:ℤ))*qInteger q (l-(t:ℤ))*qInteger q (k:ℤ)

theorem quantumCupLeftDiagonal_ladder (q : ℝ) (n : ℕ) (l h : ℤ) (t k : ℕ) :
    quantumOscillatorLadderCoefficient q (l-(t:ℤ)+h+(k:ℤ)+(n:ℤ)) t=
      quantumCupLeftDiagonal q n l h t k := by
  unfold quantumOscillatorLadderCoefficient quantumCupLeftDiagonal
  have he : -(l-(t:ℤ)+h+(k:ℤ)+(n:ℤ))-2*(t:ℤ)+2= -l-h-(t:ℤ)-(k:ℤ)-(n:ℤ)+2 := by ring
  have he' : l-(t:ℤ)+h+(k:ℤ)+(n:ℤ)+(t:ℤ)=l+h+(k:ℤ)+(n:ℤ) := by ring
  rw [he,he']

theorem quantumCupLeftOffDiagonal_cross (q : ℝ) (hq : q≠0) (n : ℕ) (l h c : ℤ) (t k : ℕ) :
    (q^(-2:ℤ))^t*(qGeometricInteger q (k:ℤ)*
      ((-1:ℝ)^n*q^(-(n:ℤ)-h-(c-(k:ℤ)))*qInteger q (l-(t:ℤ))))=
      quantumCupLeftOffDiagonal q n l h c t k := by
  have hQ : (q^(-2:ℤ))^t=q^(-2*(t:ℤ)) := by rw [zpow_mul,zpow_natCast]
  rw [hQ]
  unfold qGeometricInteger quantumCupLeftOffDiagonal
  have hp : q^(-2*(t:ℤ))*(q^(1-(k:ℤ))*q^(-(n:ℤ)-h-(c-(k:ℤ))))=
      q^(1-(n:ℤ)-h-c-2*(t:ℤ)) := by
    simp only [← zpow_add₀ hq]
    congr 1
    ring
  calc
    _ = ((-1:ℝ)^n*qInteger q (l-(t:ℤ))*qInteger q (k:ℤ))*
      (q^(-2*(t:ℤ))*(q^(1-(k:ℤ))*q^(-(n:ℤ)-h-(c-(k:ℤ))))) := by ring
    _ = _ := by rw [hp];ring

theorem quantumCupRightPart_left_homogeneous (q : ℝ) (n : ℕ) (l h c : ℤ) (t k : ℕ) :
    CoefficientHomogeneous (tripleLeftDegree n) (l-(t:ℤ)+h+(k:ℤ))
      (((tripleRightCreation q n)^k) (tripleCupBase n (l-(t:ℤ)) h (c-(k:ℤ)))) :=
  tripleRightCreation_pow_left_homogeneous q n (l-(t:ℤ)+h) _
    (tripleCupBase_left_homogeneous n (l-(t:ℤ)) h (c-(k:ℤ))) k

end AMSPhysical
