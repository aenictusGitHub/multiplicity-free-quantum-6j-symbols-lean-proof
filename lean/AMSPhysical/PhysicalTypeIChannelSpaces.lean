import QuantumTripleGeneralChannels
import QuantumCompleteHighestSimpleSpectrum
import QuantumCupStandardEigenvalues

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical

def physicalTypeILeftIndex (l m h c : ℕ) (t : QuantumCupIndex l m c) : MixedFusionIndex l (m+h) :=
  ⟨t.val.val,by have ht:=t.val.isLt;have hl:=t.property.1;omega⟩

def physicalTypeIRightIndex (l m h c : ℕ) (t : QuantumCupIndex l m c) : MixedFusionIndex (m+h) c :=
  ⟨m-t.val.val,by have ht:=t.val.isLt;have hc:=t.property.2;omega⟩

def physicalTypeILeftChannelSpace (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n l m h c : ℕ)
    (t : QuantumCupIndex l m c) : Submodule ℝ (physicalQuantumHighestMultiplicity q hq hD n l m h c) :=
  Submodule.comap (physicalQuantumHighestMultiplicity q hq hD n l m h c).subtype
    (physicalTripleLeftChannelGeneral q hq hD n l (m+h) c (physicalTypeILeftIndex l m h c t))

def physicalTypeIRightChannelSpace (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n l m h c : ℕ)
    (t : QuantumCupIndex l m c) : Submodule ℝ (physicalQuantumHighestMultiplicity q hq hD n l m h c) :=
  Submodule.comap (physicalQuantumHighestMultiplicity q hq hD n l m h c).subtype
    (physicalTripleRightChannelGeneral q hq hD n l (m+h) c (physicalTypeIRightIndex l m h c t))

theorem completeHighestLeftAction_eigenspace_eq_channel (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m h c : ℕ) (hadm : m≤l+c) (hRank : h=0 ∨ n=1) (t : QuantumCupIndex l m c) :
    Module.End.eigenspace (R:=ℝ)
      (M:=physicalQuantumHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m h c)
      (completeHighestLeftAction q hq hq1 n hn l m h c hadm hRank) (quantumCupLeftEigenvalue q n l m h t.val.val)=
      physicalTypeILeftChannelSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m h c t := by
  ext v
  rw [Module.End.mem_eigenspace_iff]
  change _ ↔ v.val∈physicalTripleLeftChannelGeneral q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
    n l (m+h) c (physicalTypeILeftIndex l m h c t)
  rw [← physicalTripleLeftRadialTotal_eigenspace q hq hq1 n hn,Module.End.mem_eigenspace_iff,Subtype.ext_iff]
  simp only [Submodule.coe_smul_of_tower,completeHighestLeftAction_ambient]
  rw [quantumCupLeftEigenvalue_middle_add q n l m h]
  rfl

theorem completeHighestRightAction_eigenspace_eq_channel (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m h c : ℕ) (hadm : m≤l+c) (hRank : h=0 ∨ n=1) (t : QuantumCupIndex l m c) :
    Module.End.eigenspace (R:=ℝ)
      (M:=physicalQuantumHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m h c)
      (completeHighestRightAction q hq hq1 n hn l m h c hadm hRank) (quantumCupLeftEigenvalue q n c m h (m-t.val.val))=
      physicalTypeIRightChannelSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m h c t := by
  ext v
  rw [Module.End.mem_eigenspace_iff]
  change _ ↔ v.val∈physicalTripleRightChannelGeneral q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
    n l (m+h) c (physicalTypeIRightIndex l m h c t)
  rw [← physicalTripleRightRadialTotal_eigenspace q hq hq1 n hn,Module.End.mem_eigenspace_iff,Subtype.ext_iff]
  simp only [Submodule.coe_smul_of_tower,completeHighestRightAction_ambient]
  rw [quantumCupLeftEigenvalue_middle_add q n c m h]
  rw [quantumCupLeftEigenvalue_swap q n c (m+h)]
  rfl

end AMSPhysical
#print axioms AMSPhysical.completeHighestLeftAction_eigenspace_eq_channel
#print axioms AMSPhysical.completeHighestRightAction_eigenspace_eq_channel
