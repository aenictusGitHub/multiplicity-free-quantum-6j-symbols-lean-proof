import QuantumFiniteTripleAdjunction
import ScaledAdjointRadial

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical

def finiteTripleLeftRadial (q : ℝ) (n l m c : ℕ) : Module.End ℝ (quantumOccupationTripleSpace n (l+1) (m+1) c) :=
  (finiteTripleLeftCreation q n l m c).comp (finiteTripleLeftAnnihilation q n l m c)

def finiteTripleRightRadial (q : ℝ) (n l m c : ℕ) : Module.End ℝ (quantumOccupationTripleSpace n l (m+1) (c+1)) :=
  (finiteTripleRightCreation q n l m c).comp (finiteTripleRightAnnihilation q n l m c)

theorem occupationTripleCoefficients_leftRadial (q : ℝ) (n l m c : ℕ) (v : quantumOccupationTripleSpace n (l+1) (m+1) c) :
    occupationTripleCoefficients n (l+1) (m+1) c (finiteTripleLeftRadial q n l m c v)=
      tripleLeftCreation q n (tripleLeftAnnihilation q n (occupationTripleCoefficients n (l+1) (m+1) c v)) := by
  rw [finiteTripleLeftRadial,LinearMap.comp_apply,occupationTripleCoefficients_leftCreation,occupationTripleCoefficients_leftAnnihilation]

theorem occupationTripleCoefficients_rightRadial (q : ℝ) (n l m c : ℕ) (v : quantumOccupationTripleSpace n l (m+1) (c+1)) :
    occupationTripleCoefficients n l (m+1) (c+1) (finiteTripleRightRadial q n l m c v)=
      tripleRightCreation q n (tripleRightAnnihilation q n (occupationTripleCoefficients n l (m+1) (c+1) v)) := by
  rw [finiteTripleRightRadial,LinearMap.comp_apply,occupationTripleCoefficients_rightCreation,occupationTripleCoefficients_rightAnnihilation]

theorem finiteTripleLeftRadial_selfAdjoint (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n l m c : ℕ)
    (u v : quantumOccupationTripleSpace n (l+1) (m+1) c) :
    physicalTripleBilin q n (l+1) (m+1) c (finiteTripleLeftRadial q n l m c u) v=
      physicalTripleBilin q n (l+1) (m+1) c u (finiteTripleLeftRadial q n l m c v) := by
  let V := quantumOccupationTripleSpace n l m c
  let W := quantumOccupationTripleSpace n (l+1) (m+1) c
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  letI : AddCommGroup W := inferInstance
  letI : Module ℝ W := inferInstance
  exact scaledAdjoint_radial_selfAdjoint (V:=V) (W:=W) (physicalTripleBilin q n l m c)
    (physicalTripleBilin q n (l+1) (m+1) c) (physicalTripleBilin_symm q n l m c)
    (physicalTripleBilin_symm q n (l+1) (m+1) c)
    (finiteTripleLeftCreation q n l m c) (finiteTripleLeftAnnihilation q n l m c)
    (mixedAnnihilationScale q n l m) (finiteTripleLeftAnnihilation_adjoint q hq hq1 n l m c) u v

theorem finiteTripleRightRadial_selfAdjoint (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n l m c : ℕ)
    (u v : quantumOccupationTripleSpace n l (m+1) (c+1)) :
    physicalTripleBilin q n l (m+1) (c+1) (finiteTripleRightRadial q n l m c u) v=
      physicalTripleBilin q n l (m+1) (c+1) u (finiteTripleRightRadial q n l m c v) := by
  let V := quantumOccupationTripleSpace n l m c
  let W := quantumOccupationTripleSpace n l (m+1) (c+1)
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  letI : AddCommGroup W := inferInstance
  letI : Module ℝ W := inferInstance
  exact scaledAdjoint_radial_selfAdjoint (V:=V) (W:=W) (physicalTripleBilin q n l m c)
    (physicalTripleBilin q n l (m+1) (c+1)) (physicalTripleBilin_symm q n l m c)
    (physicalTripleBilin_symm q n l (m+1) (c+1))
    (finiteTripleRightCreation q n l m c) (finiteTripleRightAnnihilation q n l m c)
    (mixedAnnihilationScale q n m c) (finiteTripleRightAnnihilation_adjoint q hq hq1 n l m c) u v

end AMSPhysical
