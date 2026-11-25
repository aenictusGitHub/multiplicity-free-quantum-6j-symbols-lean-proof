import StandardCupHighestVectors

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical

/-- Normalized physical highest vectors in the phase convention transported
by the explicit simultaneous radial isometry. Channel membership is a
separate theorem; no candidate factorial sum occurs in this definition. -/
def physicalTypeILeftCoupling (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l m h c : ℕ) (hadm : m≤l+c) (hRank : h=0 ∨ n=1) (t : QuantumCupIndex l m c) :
    physicalQuantumHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m h c :=
  (fullPhysicalHighestToStandard q hq hq1 n hn l m h c hadm hRank).symm
    (standardCupLeftHighest q hq hq1 l m (h+n-1) c hadm t)

def physicalTypeIRightCoupling (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l m h c : ℕ) (hadm : m≤l+c) (hRank : h=0 ∨ n=1) (t : QuantumCupIndex l m c) :
    physicalQuantumHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m h c :=
  (fullPhysicalHighestToStandard q hq hq1 n hn l m h c hadm hRank).symm
    (standardCupRightHighest q hq hq1 l m (h+n-1) c hadm t)

theorem physicalTypeILeftCoupling_unit (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l m h c : ℕ) (hadm : m≤l+c) (hRank : h=0 ∨ n=1) (t : QuantumCupIndex l m c) :
    physicalTripleBilin q n l (m+h) c (physicalTypeILeftCoupling q hq hq1 n hn l m h c hadm hRank t).val
      (physicalTypeILeftCoupling q hq hq1 n hn l m h c hadm hRank t).val=1 := by
  have he:=fullPhysicalHighestToStandard_isometry q hq hq1 n hn l m h c hadm hRank
    (physicalTypeILeftCoupling q hq hq1 n hn l m h c hadm hRank t)
    (physicalTypeILeftCoupling q hq hq1 n hn l m h c hadm hRank t)
  unfold physicalTypeILeftCoupling at he
  rw [LinearEquiv.apply_symm_apply,standardCupLeftHighest_unit] at he
  exact he.symm

theorem physicalTypeIRightCoupling_unit (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l m h c : ℕ) (hadm : m≤l+c) (hRank : h=0 ∨ n=1) (t : QuantumCupIndex l m c) :
    physicalTripleBilin q n l (m+h) c (physicalTypeIRightCoupling q hq hq1 n hn l m h c hadm hRank t).val
      (physicalTypeIRightCoupling q hq hq1 n hn l m h c hadm hRank t).val=1 := by
  have he:=fullPhysicalHighestToStandard_isometry q hq hq1 n hn l m h c hadm hRank
    (physicalTypeIRightCoupling q hq hq1 n hn l m h c hadm hRank t)
    (physicalTypeIRightCoupling q hq hq1 n hn l m h c hadm hRank t)
  unfold physicalTypeIRightCoupling at he
  rw [LinearEquiv.apply_symm_apply,standardCupRightHighest_unit] at he
  exact he.symm

theorem physicalTypeILeftCoupling_rank_image (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l m h c : ℕ) (hadm : m≤l+c) (hRank : h=0 ∨ n=1) (t : QuantumCupIndex l m c) :
    fullPhysicalHighestRankReduction q hq hq1 n hn l m h c hadm hRank
      (physicalTypeILeftCoupling q hq hq1 n hn l m h c hadm hRank t)=
      rankTwoHighestEquiv q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
        l (m+(h+n-1)) c (l+c-m+(h+n-1)) (standardCupLeftHighest q hq hq1 l m (h+n-1) c hadm t) := by
  unfold physicalTypeILeftCoupling fullPhysicalHighestToStandard
  simp only [LinearEquiv.symm_trans_apply,LinearEquiv.symm_symm,LinearEquiv.apply_symm_apply]

theorem physicalTypeIRightCoupling_rank_image (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l m h c : ℕ) (hadm : m≤l+c) (hRank : h=0 ∨ n=1) (t : QuantumCupIndex l m c) :
    fullPhysicalHighestRankReduction q hq hq1 n hn l m h c hadm hRank
      (physicalTypeIRightCoupling q hq hq1 n hn l m h c hadm hRank t)=
      rankTwoHighestEquiv q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
        l (m+(h+n-1)) c (l+c-m+(h+n-1)) (standardCupRightHighest q hq hq1 l m (h+n-1) c hadm t) := by
  unfold physicalTypeIRightCoupling fullPhysicalHighestToStandard
  simp only [LinearEquiv.symm_trans_apply,LinearEquiv.symm_symm,LinearEquiv.apply_symm_apply]

theorem physicalTypeICoupling_overlap_rankTwo (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l m h c : ℕ) (hadm : m≤l+c) (hRank : h=0 ∨ n=1) (s t : QuantumCupIndex l m c) :
    physicalTripleBilin q n l (m+h) c (physicalTypeILeftCoupling q hq hq1 n hn l m h c hadm hRank s).val
      (physicalTypeIRightCoupling q hq hq1 n hn l m h c hadm hRank t).val=
      quantumRacahMatrix q hq hq1 l (m+(h+n-1)) c
        (quantumCupLeftPath l m (h+n-1) c s) (quantumCupRightPath l m (h+n-1) c t) := by
  have he:=fullPhysicalHighestToStandard_isometry q hq hq1 n hn l m h c hadm hRank
    (physicalTypeILeftCoupling q hq hq1 n hn l m h c hadm hRank s)
    (physicalTypeIRightCoupling q hq hq1 n hn l m h c hadm hRank t)
  unfold physicalTypeILeftCoupling physicalTypeIRightCoupling at he
  rw [LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply,standardCupHighest_overlap] at he
  exact he.symm

end AMSPhysical
#print axioms AMSPhysical.physicalTypeICoupling_overlap_rankTwo
