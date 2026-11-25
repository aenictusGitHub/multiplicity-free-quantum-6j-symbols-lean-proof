import QuantumTripleExactChannels
import QuantumTripleZeroBoundaries
import QuantumPhysicalTripleInstances

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical

/-- Actual intermediate-channel subspaces, with the whole tensor space at
the one-channel zero-external-degree boundaries. -/
def physicalTripleLeftChannelGeneral (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n l m c : ℕ)
    (r : MixedFusionIndex l m) : Submodule ℝ (quantumOccupationTripleSpace n l m c) :=
  match l,m with
  | 0,_ => ⊤
  | _+1,0 => ⊤
  | a+1,b+1 => physicalTripleLeftChannel q hq hD n a b c r

def physicalTripleRightChannelGeneral (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n l m c : ℕ)
    (r : MixedFusionIndex m c) : Submodule ℝ (quantumOccupationTripleSpace n l m c) :=
  match m,c with
  | 0,_ => ⊤
  | _+1,0 => ⊤
  | a+1,b+1 => physicalTripleRightChannel q hq hD n l a b r

theorem physicalTripleLeftRadialTotal_eigenspace (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m c : ℕ) (r : MixedFusionIndex l m) :
    Module.End.eigenspace (R:=ℝ) (M:=quantumOccupationTripleSpace n l m c)
      (physicalTripleLeftRadialTotal q n l m c) (quantumCupLeftEigenvalue q n l m 0 r.val)=
      physicalTripleLeftChannelGeneral q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m c r := by
  cases l with
  | zero =>
    have hr : r.val=0 := by have hh:=r.isLt;omega
    rw [physicalTripleLeftRadialTotal_zero_first]
    simp [quantumCupLeftEigenvalue,hr,Module.End.eigenspace_def,physicalTripleLeftChannelGeneral]
  | succ l =>
    cases m with
    | zero =>
      have hr : r.val=0 := by have hh:=r.isLt;omega
      rw [physicalTripleLeftRadialTotal_zero_middle]
      simp [quantumCupLeftEigenvalue,hr,Module.End.eigenspace_def,physicalTripleLeftChannelGeneral]
    | succ m =>
      rw [physicalTripleLeftRadialTotal_positive]
      exact finiteTripleLeftRadial_eigenspace q hq hq1 n hn l m c r

theorem physicalTripleRightRadialTotal_eigenspace (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m c : ℕ) (r : MixedFusionIndex m c) :
    Module.End.eigenspace (R:=ℝ) (M:=quantumOccupationTripleSpace n l m c)
      (physicalTripleRightRadialTotal q n l m c) (quantumCupLeftEigenvalue q n m c 0 r.val)=
      physicalTripleRightChannelGeneral q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m c r := by
  cases m with
  | zero =>
    have hr : r.val=0 := by have hh:=r.isLt;omega
    rw [physicalTripleRightRadialTotal_zero_middle]
    simp [quantumCupLeftEigenvalue,hr,Module.End.eigenspace_def,physicalTripleRightChannelGeneral]
  | succ m =>
    cases c with
    | zero =>
      have hr : r.val=0 := by have hh:=r.isLt;omega
      rw [physicalTripleRightRadialTotal_zero_third]
      simp [quantumCupLeftEigenvalue,hr,Module.End.eigenspace_def,physicalTripleRightChannelGeneral]
    | succ c =>
      rw [physicalTripleRightRadialTotal_positive]
      exact finiteTripleRightRadial_eigenspace q hq hq1 n hn l m c r

end AMSPhysical
#print axioms AMSPhysical.physicalTripleLeftRadialTotal_eigenspace
#print axioms AMSPhysical.physicalTripleRightRadialTotal_eigenspace
