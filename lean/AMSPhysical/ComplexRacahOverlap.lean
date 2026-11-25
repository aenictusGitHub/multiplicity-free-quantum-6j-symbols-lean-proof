import ComplexTreeCoefficients
import QuantumTripleBasisSum

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
noncomputable section
namespace AMSPhysical

def complexQuantumWeight (q:ℂ) (L k:ℕ):ℂ:=
  q^(quantumWeightExponent L k)*complexQfactorial q k*complexQfactorial q (L-k)/complexQfactorial q L

theorem complexQuantumWeight_ofReal (q:ℝ) (L k:ℕ):
    complexQuantumWeight (q:ℂ) L k=(quantumWeight q L k:ℂ):=by
  simp only [complexQuantumWeight,quantumWeight,complexQfactorial_ofReal,Complex.ofReal_mul,
    Complex.ofReal_div,Complex.ofReal_zpow]

/-- Independent finite overlap of the two complex CG trees in the actual
bilinear quantum weight metric. No Racah or AMS closed sum is used. -/
def complexRacahOverlap (q:ℂ) (l m n:ℕ) (p:LeftHighestPath l m n) (a:RightHighestPath l m n):ℂ:=
  ∑ i:Fin (l+1),∑ j:Fin (m+1),∑ k:Fin (n+1),
    complexQuantumWeight q l i.val*complexQuantumWeight q m j.val*complexQuantumWeight q n k.val*
      complexLeftTreeCoefficient q l m n p i j k*complexRightTreeCoefficient q l m n a i j k

theorem complexRacahOverlap_ofReal_actual (q:ℝ) (hq:0<q) (hq1:q≠1) (l m n:ℕ)
    (p:LeftHighestPath l m n) (a:RightHighestPath l m n):
    complexRacahOverlap (q:ℂ) l m n p a=(quantumRacahMatrix q hq hq1 l m n p a:ℂ):=by
  change _=(quantumTripleBilin q l m n (quantumLeftTreeHighest q hq hq1 l m n p.1 p.2)
    (quantumRightTreeHighest q hq hq1 l m n a.1 a.2):ℂ)
  rw [quantumTripleBilin_basis_sum]
  unfold complexRacahOverlap
  simp only [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  rw [complexQuantumWeight_ofReal,complexQuantumWeight_ofReal,complexQuantumWeight_ofReal,
    complexLeftTreeCoefficient_ofReal_actual q hq hq1,complexRightTreeCoefficient_ofReal_actual q hq hq1]
  simp only [Complex.ofReal_mul]

end AMSPhysical
#print axioms AMSPhysical.complexRacahOverlap_ofReal_actual
