import TypeIIShiftedCreationGramForm
import TypeIIShiftedRightUnitNorm
import TypeIIRightSpectrumDistinct

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 80000
noncomputable section
namespace AMSPhysical

/-- The actual higher-rank right channel is carried to the independent
AMS shifted standard right channel, with one real unit phase per channel. -/
theorem typeIIShiftedUnitEquiv_right (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h a b c d:ℕ) (hbal:a+b=c+d) (t:QuantumCupIndex a c b):
    ∃ e:ℝ,(e=1 ∨ e= -1) ∧
      typeIIShiftedUnitEquiv q hq hq1 h a b c d hbal
        (physicalTypeIIRightCoupling q hq hq1 (h+1) (by omega) a b c d hbal t)=
        e • typeIIStandardShiftedRightHighest q hq hq1 h a b c d hbal t := by
  let V:=physicalTypeIIHighestSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) a b c d
  letI:AddCommGroup V:=inferInstance
  letI:Module ℝ V:=inferInstance
  let W:=standardTypeAHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (a+h) (b+h) c d
  letI:AddCommGroup W:=inferInstance
  letI:Module ℝ W:=inferInstance
  let B:=restrictedBilinearPair (quantumTripleBilin q (a+h) (b+h) c) W
  let G:=typeIIShiftedCreationGramForm q hq hq1 h a b c d
  let E:=typeIIShiftedUnitEquiv q hq hq1 h a b c d hbal
  let v:=physicalTypeIIRightCoupling q hq hq1 (h+1) (by omega) a b c d hbal t
  have hb:∀ i j,B (typeIIStandardShiftedRightBasis q hq hq1 h a b c d hbal i)
      (typeIIStandardShiftedRightBasis q hq hq1 h a b c d hbal j)=if i=j then 1 else 0:=by
    intro i j
    rw [typeIIStandardShiftedRightBasis_apply,typeIIStandardShiftedRightBasis_apply]
    exact typeIIStandardShiftedRightHighest_pair q hq hq1 h a b c d hbal i j
  have hbg:∀ x i,G x (typeIIStandardShiftedRightBasis q hq hq1 h a b c d hbal i)=
      mixedCreationSpectralScalar q (h+1) b c (c-i.val.val)*
        B x (typeIIStandardShiftedRightBasis q hq hq1 h a b c d hbal i):=by
    intro x i
    rw [typeIIStandardShiftedRightBasis_apply]
    exact typeIIShiftedCreationGramForm_standardRight q hq hq1 h a b c d hbal x i
  have hn:B (E v) (E v)=1:=typeIIShiftedUnitEquiv_right_unit q hq hq1 h a b c d hbal t
  obtain ⟨e,he,hv⟩:=gramEigen_unit_unique_sign (I:=QuantumCupIndex a c b) (V:=W) B G
    (fun x y=>quantumTripleBilin_symm q hq hq1 (a+h) (b+h) c x.val y.val)
    (typeIIShiftedCreationGramForm_symm q hq hq1 h a b c d)
    (typeIIStandardShiftedRightBasis q hq hq1 h a b c d hbal) hb
    (fun i:QuantumCupIndex a c b=>mixedCreationSpectralScalar q (h+1) b c (c-i.val.val))
    (typeIIRightCreationSpectrum_injective q hq hq1 (h+1) (by omega) a b c) hbg t (E v)
    (fun x=>typeIIShiftedCreationGramForm_physicalRight q hq hq1 h a b c d hbal x t) hn
  refine ⟨e,he,?_⟩
  rwa [typeIIStandardShiftedRightBasis_apply] at hv

end AMSPhysical
#print axioms AMSPhysical.typeIIShiftedUnitEquiv_right
