import TypeIIStandardShiftedBasis

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
noncomputable section
namespace AMSPhysical

def typeIIStandardShiftedRightHighest (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h a b c d:ℕ) (hbal:a+b=c+d) (t:QuantumCupIndex a c b):
    standardTypeAHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (a+h) (b+h) c d := by
  let p:=typeIIShiftedRightPath h a b c t
  refine ⟨quantumRightTreeHighest q hq hq1 (a+h) (b+h) c p.1 p.2,?_⟩
  apply (standardTypeAHighest_mem_iff q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (a+h) (b+h) c d _).mpr
  refine ⟨quantumRightTreeHighest_E q hq hq1 (a+h) (b+h) c p,?_⟩
  have he:=quantumRightTreeHighest_K q hq hq1 (a+h) (b+h) c p
  change _=q^(rightTotalLabel (a+h) (b+h) c p:ℤ) • _ at he
  rw [typeIIShiftedRight_total h a b c d hbal t] at he
  exact he

theorem typeIIShiftedRightEmbedding_injective (h a b c:ℕ):
    Function.Injective (fun t:QuantumCupIndex a c b=>
      rightHighestEmbedding (a+h) (b+h) c (typeIIShiftedRightPath h a b c t)) := by
  intro s t he
  have hp:=(rightHighestEmbedding_injective (a+h) (b+h) c) he
  have hs:=s.val.isLt
  have ht:=t.val.isLt
  have hv:=congrArg (fun p:RightHighestPath (a+h) (b+h) c=>p.1.val) hp
  change c-s.val.val=c-t.val.val at hv
  apply Subtype.ext
  apply Fin.ext
  omega

theorem typeIIStandardShiftedRightHighest_pair (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h a b c d:ℕ) (hbal:a+b=c+d) (s t:QuantumCupIndex a c b):
    quantumTripleBilin q (a+h) (b+h) c
      (typeIIStandardShiftedRightHighest q hq hq1 h a b c d hbal s).val
      (typeIIStandardShiftedRightHighest q hq hq1 h a b c d hbal t).val=if s=t then 1 else 0 := by
  classical
  simpa only [rightFusionHighest_eq,(typeIIShiftedRightEmbedding_injective h a b c).eq_iff] using
    rightFusionVector_pair q hq hq1 (a+h) (b+h) c
      (rightHighestEmbedding (a+h) (b+h) c (typeIIShiftedRightPath h a b c s))
      (rightHighestEmbedding (a+h) (b+h) c (typeIIShiftedRightPath h a b c t))

/-- Complete independent right coupling basis at the AMS shifted labels. -/
def typeIIStandardShiftedRightBasis (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h a b c d:ℕ) (hbal:a+b=c+d):
    Module.Basis (QuantumCupIndex a c b) ℝ
      (standardTypeAHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (a+h) (b+h) c d) := by
  let V:=standardTypeAHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (a+h) (b+h) c d
  letI:AddCommGroup V:=inferInstance
  letI:Module ℝ V:=inferInstance
  have hi:LinearIndependent ℝ (typeIIStandardShiftedRightHighest q hq hq1 h a b c d hbal):=
    bilinear_orthonormal_independent (V:=V)
      (restrictedBilinearPair (quantumTripleBilin q (a+h) (b+h) c) V)
      (typeIIStandardShiftedRightHighest q hq hq1 h a b c d hbal)
      (typeIIStandardShiftedRightHighest_pair q hq hq1 h a b c d hbal)
  letI:Nonempty (QuantumCupIndex a c b):=⟨quantumCupTop a c b (by omega)⟩
  refine basisOfLinearIndependentOfCardEqFinrank hi ?_
  rw [Module.finrank_eq_card_basis (typeIIStandardShiftedLeftBasis q hq hq1 h a b c d hbal)]
  exact (Fintype.card_congr (typeIICommonCupEquiv a b c d hbal)).symm

theorem typeIIStandardShiftedRightBasis_apply (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h a b c d:ℕ) (hbal:a+b=c+d) (t:QuantumCupIndex a c b):
    typeIIStandardShiftedRightBasis q hq hq1 h a b c d hbal t=
      typeIIStandardShiftedRightHighest q hq hq1 h a b c d hbal t := by
  letI:Nonempty (QuantumCupIndex a c b):=⟨quantumCupTop a c b (by omega)⟩
  rw [typeIIStandardShiftedRightBasis,coe_basisOfLinearIndependentOfCardEqFinrank]

end AMSPhysical
#print axioms AMSPhysical.typeIIStandardShiftedRightBasis
