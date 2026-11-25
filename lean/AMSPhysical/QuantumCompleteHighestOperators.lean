import QuantumFullHighestRankReduction

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical

theorem transported_conjugate_intertwines
    {V W C D : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    [AddCommGroup C] [Module ℝ C] [AddCommGroup D] [Module ℝ D]
    (e : V ≃ₗ[ℝ] C) (f : W ≃ₗ[ℝ] D) (S : V ≃ₗ[ℝ] W) (T : C ≃ₗ[ℝ] D)
    (hS : ∀ v,f (S v)=T (e v)) (A : Module.End ℝ C) (B : Module.End ℝ D)
    (hT : ∀ c,T (A c)=B (T c)) (v : V) :
    S (e.symm.conj A v)=f.symm.conj B (S v) := by
  apply f.injective
  simp only [LinearEquiv.conj_apply,LinearEquiv.symm_symm,LinearMap.comp_apply,LinearEquiv.coe_coe,hS,LinearEquiv.apply_symm_apply]
  exact hT (e v)

abbrev physicalQuantumHighestMultiplicity (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (n l m h c : ℕ) :=
  typeAHighestSpace (V:=quantumOccupationTripleSpace n l (m+h) c) q n
    (typeAMixedTriple q hq hD n l (m+h) c) (mixedHighestDynkin n (l+c-m+h) 0)

def completeHighestCoefficientEquiv (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m h c : ℕ) (hadm : m≤l+c) (hRank : h=0 ∨ n=1) :
    physicalQuantumHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m h c ≃ₗ[ℝ]
      quantumCupSpan q n l m h c :=
  (LinearEquiv.ofEq _ _ (physicalQuantumCupSpan_eq_highest q hq hq1 n hn l m h c hadm hRank).symm).trans
    (physicalQuantumCupCoefficientEquiv q hq n hn l m h c)

theorem completeHighestCoefficientEquiv_literal (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m h c : ℕ) (hadm : m≤l+c) (hRank : h=0 ∨ n=1)
    (v : physicalQuantumHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m h c) :
    (completeHighestCoefficientEquiv q hq hq1 n hn l m h c hadm hRank v).val=
      occupationTripleCoefficients n l (m+h) c v.val := by
  unfold completeHighestCoefficientEquiv
  simp only [LinearEquiv.trans_apply,LinearEquiv.coe_ofEq_apply]
  exact physicalQuantumCupCoefficientEquiv_literal q hq n hn l m h c _

def completeHighestLeftAction (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m h c : ℕ) (hadm : m≤l+c) (hRank : h=0 ∨ n=1) :
    Module.End ℝ (physicalQuantumHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m h c) :=
  (completeHighestCoefficientEquiv q hq hq1 n hn l m h c hadm hRank).symm.conj
    (quantumCupLeftAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m h c)

def completeHighestRightAction (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m h c : ℕ) (hadm : m≤l+c) (hRank : h=0 ∨ n=1) :
    Module.End ℝ (physicalQuantumHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m h c) :=
  (completeHighestCoefficientEquiv q hq hq1 n hn l m h c hadm hRank).symm.conj
    (quantumCupRightAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m h c)

theorem fullPhysicalHighestRankReduction_coefficients (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m h c : ℕ) (hadm : m≤l+c) (hRank : h=0 ∨ n=1)
    (v : physicalQuantumHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m h c) :
    completeHighestCoefficientEquiv q hq hq1 1 (by omega) l m (h+n-1) c hadm (Or.inr rfl)
      (fullPhysicalHighestRankReduction q hq hq1 n hn l m h c hadm hRank v)=
      quantumCupUnitaryRankReduction q hq n hn l m h c hadm
        (completeHighestCoefficientEquiv q hq hq1 n hn l m h c hadm hRank v) := by
  apply Subtype.ext
  rw [completeHighestCoefficientEquiv_literal]
  unfold fullPhysicalHighestRankReduction physicalQuantumCupUnitaryRankReduction
  simp only [LinearEquiv.trans_apply,LinearEquiv.coe_ofEq_apply]
  rw [physicalQuantumCupCoefficientEquiv_inverse_literal q hq 1 (by omega) l m (h+n-1) c,
    occupationTripleCoefficients_cupSpan_synthesis q hq 1 (by omega) l m (h+n-1) c]
  rfl

theorem fullPhysicalHighestRankReduction_left (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m h c : ℕ) (hadm : m≤l+c) (hRank : h=0 ∨ n=1)
    (v : physicalQuantumHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m h c) :
    fullPhysicalHighestRankReduction q hq hq1 n hn l m h c hadm hRank
      (completeHighestLeftAction q hq hq1 n hn l m h c hadm hRank v)=
      completeHighestLeftAction q hq hq1 1 (by omega) l m (h+n-1) c hadm (Or.inr rfl)
        (fullPhysicalHighestRankReduction q hq hq1 n hn l m h c hadm hRank v) := by
  let V0 := quantumOccupationTripleSpace n l (m+h) c
  let W0 := quantumOccupationTripleSpace 1 l (m+(h+n-1)) c
  letI : AddCommGroup V0 := inferInstance
  letI : Module ℝ V0 := inferInstance
  letI : AddCommGroup W0 := inferInstance
  letI : Module ℝ W0 := inferInstance
  let V : Type := physicalQuantumHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m h c
  let W : Type := physicalQuantumHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) 1 l m (h+n-1) c
  let C : Type := quantumCupSpan q n l m h c
  let D : Type := quantumCupSpan q 1 l m (h+n-1) c
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  letI : AddCommGroup W := inferInstance
  letI : Module ℝ W := inferInstance
  letI : AddCommGroup C := inferInstance
  letI : Module ℝ C := inferInstance
  letI : AddCommGroup D := inferInstance
  letI : Module ℝ D := inferInstance
  exact transported_conjugate_intertwines (V:=V) (W:=W) (C:=C) (D:=D)
    (completeHighestCoefficientEquiv q hq hq1 n hn l m h c hadm hRank)
    (completeHighestCoefficientEquiv q hq hq1 1 (by omega) l m (h+n-1) c hadm (Or.inr rfl))
    (fullPhysicalHighestRankReduction q hq hq1 n hn l m h c hadm hRank)
    (quantumCupUnitaryRankReduction q hq n hn l m h c hadm)
    (fullPhysicalHighestRankReduction_coefficients q hq hq1 n hn l m h c hadm hRank)
    _ _ (quantumCupUnitaryRankReduction_left q hq hq1 n hn l m h c hadm) v

theorem fullPhysicalHighestRankReduction_right (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m h c : ℕ) (hadm : m≤l+c) (hRank : h=0 ∨ n=1)
    (v : physicalQuantumHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m h c) :
    fullPhysicalHighestRankReduction q hq hq1 n hn l m h c hadm hRank
      (completeHighestRightAction q hq hq1 n hn l m h c hadm hRank v)=
      completeHighestRightAction q hq hq1 1 (by omega) l m (h+n-1) c hadm (Or.inr rfl)
        (fullPhysicalHighestRankReduction q hq hq1 n hn l m h c hadm hRank v) := by
  let V0 := quantumOccupationTripleSpace n l (m+h) c
  let W0 := quantumOccupationTripleSpace 1 l (m+(h+n-1)) c
  letI : AddCommGroup V0 := inferInstance
  letI : Module ℝ V0 := inferInstance
  letI : AddCommGroup W0 := inferInstance
  letI : Module ℝ W0 := inferInstance
  let V : Type := physicalQuantumHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m h c
  let W : Type := physicalQuantumHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) 1 l m (h+n-1) c
  let C : Type := quantumCupSpan q n l m h c
  let D : Type := quantumCupSpan q 1 l m (h+n-1) c
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  letI : AddCommGroup W := inferInstance
  letI : Module ℝ W := inferInstance
  letI : AddCommGroup C := inferInstance
  letI : Module ℝ C := inferInstance
  letI : AddCommGroup D := inferInstance
  letI : Module ℝ D := inferInstance
  exact transported_conjugate_intertwines (V:=V) (W:=W) (C:=C) (D:=D)
    (completeHighestCoefficientEquiv q hq hq1 n hn l m h c hadm hRank)
    (completeHighestCoefficientEquiv q hq hq1 1 (by omega) l m (h+n-1) c hadm (Or.inr rfl))
    (fullPhysicalHighestRankReduction q hq hq1 n hn l m h c hadm hRank)
    (quantumCupUnitaryRankReduction q hq n hn l m h c hadm)
    (fullPhysicalHighestRankReduction_coefficients q hq hq1 n hn l m h c hadm hRank)
    _ _ (quantumCupUnitaryRankReduction_right q hq hq1 n hn l m h c hadm) v

end AMSPhysical
#print axioms AMSPhysical.fullPhysicalHighestRankReduction_left
#print axioms AMSPhysical.fullPhysicalHighestRankReduction_right
