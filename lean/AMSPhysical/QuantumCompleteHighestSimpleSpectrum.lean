import QuantumCompleteHighestOperators
import QuantumPhysicalTripleInstances
import QuantumCupRightSimpleSpectrum
import LinearEigenspaceTransport

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical

theorem equiv_conjugate_action {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (e : V ≃ₗ[ℝ] W) (A : Module.End ℝ W) (v : V) : e (e.symm.conj A v)=A (e v) := by
  simp only [LinearEquiv.conj_apply,LinearEquiv.symm_symm,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply]

theorem completeHighestLeftAction_eigenspace_finrank (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m h c : ℕ) (hadm : m≤l+c) (hRank : h=0 ∨ n=1) (t : QuantumCupIndex l m c) :
    Module.finrank ℝ (Module.End.eigenspace (R:=ℝ)
      (M:=physicalQuantumHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m h c)
      (completeHighestLeftAction q hq hq1 n hn l m h c hadm hRank)
      (quantumCupLeftEigenvalue q n l m h t.val.val))=1 := by
  let V0 := quantumOccupationTripleSpace n l (m+h) c
  letI : AddCommGroup V0 := inferInstance
  letI : Module ℝ V0 := inferInstance
  let V : Type := physicalQuantumHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m h c
  let W : Type := quantumCupSpan q n l m h c
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  letI : AddCommGroup W := inferInstance
  letI : Module ℝ W := inferInstance
  let e:=completeHighestCoefficientEquiv q hq hq1 n hn l m h c hadm hRank
  have he:=eigenspaceIntertwinerEquiv (V:=V) (W:=W) e
    (completeHighestLeftAction q hq hq1 n hn l m h c hadm hRank)
    (quantumCupLeftAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m h c)
    (equiv_conjugate_action e _) (quantumCupLeftEigenvalue q n l m h t.val.val)
  exact he.finrank_eq.trans (quantumCupLeftAction_eigenspace_finrank q hq hq1 n hn l m h c t)

theorem completeHighestRightAction_eigenspace_finrank (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m h c : ℕ) (hadm : m≤l+c) (hRank : h=0 ∨ n=1) (t : QuantumCupIndex l m c) :
    Module.finrank ℝ (Module.End.eigenspace (R:=ℝ)
      (M:=physicalQuantumHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m h c)
      (completeHighestRightAction q hq hq1 n hn l m h c hadm hRank)
      (quantumCupLeftEigenvalue q n c m h (m-t.val.val)))=1 := by
  let V0 := quantumOccupationTripleSpace n l (m+h) c
  letI : AddCommGroup V0 := inferInstance
  letI : Module ℝ V0 := inferInstance
  let V : Type := physicalQuantumHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m h c
  let W : Type := quantumCupSpan q n l m h c
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  letI : AddCommGroup W := inferInstance
  letI : Module ℝ W := inferInstance
  let e:=completeHighestCoefficientEquiv q hq hq1 n hn l m h c hadm hRank
  have he:=eigenspaceIntertwinerEquiv (V:=V) (W:=W) e
    (completeHighestRightAction q hq hq1 n hn l m h c hadm hRank)
    (quantumCupRightAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m h c)
    (equiv_conjugate_action e _) (quantumCupLeftEigenvalue q n c m h (m-t.val.val))
  exact he.finrank_eq.trans (quantumCupRightAction_eigenspace_finrank q hq hq1 n hn l m h c t)

end AMSPhysical
#print axioms AMSPhysical.completeHighestLeftAction_eigenspace_finrank
#print axioms AMSPhysical.completeHighestRightAction_eigenspace_finrank
