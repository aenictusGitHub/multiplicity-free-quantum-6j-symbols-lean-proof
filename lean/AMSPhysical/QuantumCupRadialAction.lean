import QuantumCupRadialInvariant

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical

def quantumCupLeftAction (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n : ℕ) (hn : 0<n) (l m h c : ℕ) :
    Module.End ℝ (quantumCupSpan q n l m h c) :=
  LinearMap.codRestrict (quantumCupSpan q n l m h c)
    (((tripleLeftCreation q n).comp (tripleLeftAnnihilation q n)).comp (quantumCupSpan q n l m h c).subtype)
    (fun v =>quantumCupLeftRadial_preserves q hq hD n hn l m h c v.val v.property)

def quantumCupRightAction (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n : ℕ) (hn : 0<n) (l m h c : ℕ) :
    Module.End ℝ (quantumCupSpan q n l m h c) :=
  LinearMap.codRestrict (quantumCupSpan q n l m h c)
    (((tripleRightCreation q n).comp (tripleRightAnnihilation q n)).comp (quantumCupSpan q n l m h c).subtype)
    (fun v =>quantumCupRightRadial_preserves q hq hD n hn l m h c v.val v.property)

theorem quantumCupLeftAction_vector (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n : ℕ) (hn : 0<n)
    (l m h c : ℕ) (r : QuantumCupIndex l m c) :
    quantumCupLeftAction q hq hD n hn l m h c (quantumCupVector q n l m h c r)=
      quantumCupLeftDiagonal q n (l:ℤ) (h:ℤ) r.val.val (m-r.val.val) • quantumCupVector q n l m h c r+
        if hr : quantumCupCanRaiseLeft l m c r then
          quantumCupLeftOffDiagonal q n (l:ℤ) (h:ℤ) (c:ℤ) r.val.val (m-r.val.val) •
            quantumCupVector q n l m h c (quantumCupRaiseLeft l m c r hr) else 0 := by
  apply Subtype.ext
  have h0:=quantumCupLeftRadial_vector q hq hD n hn l m h c r
  by_cases hs : quantumCupCanRaiseLeft l m c r
  · simpa only [dif_pos hs,Submodule.coe_add,Submodule.coe_smul_of_tower] using h0
  · simpa only [dif_neg hs,Submodule.coe_add,Submodule.coe_smul_of_tower,Submodule.coe_zero] using h0

theorem quantumCupRightAction_vector (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n : ℕ) (hn : 0<n)
    (l m h c : ℕ) (r : QuantumCupIndex l m c) :
    quantumCupRightAction q hq hD n hn l m h c (quantumCupVector q n l m h c r)=
      quantumCupLeftDiagonal q n (c:ℤ) (h:ℤ) (m-r.val.val) r.val.val • quantumCupVector q n l m h c r+
        if hr : quantumCupCanRaiseRight l m c r then
          quantumCupLeftOffDiagonal q n (c:ℤ) (h:ℤ) (l:ℤ) (m-r.val.val) r.val.val •
            quantumCupVector q n l m h c (quantumCupRaiseRight l m c r hr) else 0 := by
  apply Subtype.ext
  have h0:=quantumCupRightRadial_vector q hq hD n hn l m h c r
  by_cases hs : quantumCupCanRaiseRight l m c r
  · simpa only [dif_pos hs,Submodule.coe_add,Submodule.coe_smul_of_tower] using h0
  · simpa only [dif_neg hs,Submodule.coe_add,Submodule.coe_smul_of_tower,Submodule.coe_zero] using h0

end AMSPhysical
