import PhysicalTypeIChannelCouplings
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical

theorem standardCupLeftHighest_pair (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m b c : ℕ) (hadm : m≤l+c)
    (s t : QuantumCupIndex l m c) :
    quantumTripleBilin q l (m+b) c (standardCupLeftHighest q hq hq1 l m b c hadm s).val
      (standardCupLeftHighest q hq hq1 l m b c hadm t).val=if s=t then 1 else 0 := by
  have hE : leftHighestEmbedding l (m+b) c (quantumCupLeftPath l m b c s)=
      leftHighestEmbedding l (m+b) c (quantumCupLeftPath l m b c t) ↔ s=t := by
    constructor
    · intro he
      have hv:=congrArg (fun x : LeftFusionIndex l (m+b) c =>x.1.val) he
      apply Subtype.ext
      exact Fin.ext hv
    · rintro rfl
      rfl
  change quantumTripleBilin q l (m+b) c
    (quantumLeftTreeHighest q hq hq1 l (m+b) c (quantumCupLeftPath l m b c s).1 (quantumCupLeftPath l m b c s).2)
    (quantumLeftTreeHighest q hq hq1 l (m+b) c (quantumCupLeftPath l m b c t).1 (quantumCupLeftPath l m b c t).2)=_
  rw [← leftFusionHighest_eq,← leftFusionHighest_eq,leftFusionVector_pair]
  simp only [hE]

theorem physicalTypeILeftCoupling_pair (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l m h c : ℕ) (hadm : m≤l+c) (hRank : h=0 ∨ n=1) (s t : QuantumCupIndex l m c) :
    physicalTripleBilin q n l (m+h) c
      (physicalTypeILeftCoupling q hq hq1 n hn l m h c hadm hRank s).val
      (physicalTypeILeftCoupling q hq hq1 n hn l m h c hadm hRank t).val=if s=t then 1 else 0 := by
  have he:=fullPhysicalHighestToStandard_isometry q hq hq1 n hn l m h c hadm hRank
    (physicalTypeILeftCoupling q hq hq1 n hn l m h c hadm hRank s)
    (physicalTypeILeftCoupling q hq hq1 n hn l m h c hadm hRank t)
  simp only [physicalTypeILeftCoupling,LinearEquiv.apply_symm_apply,standardCupLeftHighest_pair] at he
  exact he.symm

theorem standardCupRightHighest_pair (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m b c : ℕ) (hadm : m≤l+c)
    (s t : QuantumCupIndex l m c) :
    quantumTripleBilin q l (m+b) c (standardCupRightHighest q hq hq1 l m b c hadm s).val
      (standardCupRightHighest q hq hq1 l m b c hadm t).val=if s=t then 1 else 0 := by
  have hE : rightHighestEmbedding l (m+b) c (quantumCupRightPath l m b c s)=
      rightHighestEmbedding l (m+b) c (quantumCupRightPath l m b c t) ↔ s=t := by
    constructor
    · intro he
      have hv:=congrArg (fun x : RightFusionIndex l (m+b) c =>x.2.1.val) he
      apply Subtype.ext
      exact Fin.ext hv
    · rintro rfl
      rfl
  change quantumTripleBilin q l (m+b) c
    (quantumRightTreeHighest q hq hq1 l (m+b) c (quantumCupRightPath l m b c s).1 (quantumCupRightPath l m b c s).2)
    (quantumRightTreeHighest q hq hq1 l (m+b) c (quantumCupRightPath l m b c t).1 (quantumCupRightPath l m b c t).2)=_
  rw [← rightFusionHighest_eq,← rightFusionHighest_eq,rightFusionVector_pair]
  simp only [hE]

theorem physicalTypeIRightCoupling_pair (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l m h c : ℕ) (hadm : m≤l+c) (hRank : h=0 ∨ n=1) (s t : QuantumCupIndex l m c) :
    physicalTripleBilin q n l (m+h) c
      (physicalTypeIRightCoupling q hq hq1 n hn l m h c hadm hRank s).val
      (physicalTypeIRightCoupling q hq hq1 n hn l m h c hadm hRank t).val=if s=t then 1 else 0 := by
  have he:=fullPhysicalHighestToStandard_isometry q hq hq1 n hn l m h c hadm hRank
    (physicalTypeIRightCoupling q hq hq1 n hn l m h c hadm hRank s)
    (physicalTypeIRightCoupling q hq hq1 n hn l m h c hadm hRank t)
  simp only [physicalTypeIRightCoupling,LinearEquiv.apply_symm_apply,standardCupRightHighest_pair] at he
  exact he.symm

theorem physicalTypeIHighest_finrank (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l m h c : ℕ) (hadm : m≤l+c) (hRank : h=0 ∨ n=1) :
    Module.finrank ℝ (physicalQuantumHighestMultiplicity q (ne_of_gt hq)
      (qInteger_denominator_ne_zero q hq hq1) n l m h c)=Fintype.card (QuantumCupIndex l m c) := by
  unfold physicalQuantumHighestMultiplicity
  rw [← physicalQuantumCupSpan_eq_highest q hq hq1 n hn l m h c hadm hRank]
  exact Module.finrank_eq_card_basis (physicalQuantumCupBasis q hq n hn l m h c)

def physicalTypeILeftBasis (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l m h c : ℕ) (hadm : m≤l+c) (hRank : h=0 ∨ n=1) :
    Module.Basis (QuantumCupIndex l m c) ℝ
      (physicalQuantumHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m h c) := by
  letI : Nonempty (QuantumCupIndex l m c):=⟨quantumCupTop l m c hadm⟩
  exact basisOfLinearIndependentOfCardEqFinrank
    (bilinear_orthonormal_independent
      (physicalHighestPairing q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m h c)
      (physicalTypeILeftCoupling q hq hq1 n hn l m h c hadm hRank)
      (physicalTypeILeftCoupling_pair q hq hq1 n hn l m h c hadm hRank))
    (physicalTypeIHighest_finrank q hq hq1 n hn l m h c hadm hRank).symm

theorem physicalTypeILeftBasis_apply (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l m h c : ℕ) (hadm : m≤l+c) (hRank : h=0 ∨ n=1) (t : QuantumCupIndex l m c) :
    physicalTypeILeftBasis q hq hq1 n hn l m h c hadm hRank t=
      physicalTypeILeftCoupling q hq hq1 n hn l m h c hadm hRank t := by
  letI : Nonempty (QuantumCupIndex l m c):=⟨quantumCupTop l m c hadm⟩
  rw [physicalTypeILeftBasis,coe_basisOfLinearIndependentOfCardEqFinrank]

def physicalTypeIRightBasis (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l m h c : ℕ) (hadm : m≤l+c) (hRank : h=0 ∨ n=1) :
    Module.Basis (QuantumCupIndex l m c) ℝ
      (physicalQuantumHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m h c) := by
  letI : Nonempty (QuantumCupIndex l m c):=⟨quantumCupTop l m c hadm⟩
  exact basisOfLinearIndependentOfCardEqFinrank
    (bilinear_orthonormal_independent
      (physicalHighestPairing q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m h c)
      (physicalTypeIRightCoupling q hq hq1 n hn l m h c hadm hRank)
      (physicalTypeIRightCoupling_pair q hq hq1 n hn l m h c hadm hRank))
    (physicalTypeIHighest_finrank q hq hq1 n hn l m h c hadm hRank).symm

theorem physicalTypeIRightBasis_apply (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l m h c : ℕ) (hadm : m≤l+c) (hRank : h=0 ∨ n=1) (t : QuantumCupIndex l m c) :
    physicalTypeIRightBasis q hq hq1 n hn l m h c hadm hRank t=
      physicalTypeIRightCoupling q hq hq1 n hn l m h c hadm hRank t := by
  letI : Nonempty (QuantumCupIndex l m c):=⟨quantumCupTop l m c hadm⟩
  rw [physicalTypeIRightBasis,coe_basisOfLinearIndependentOfCardEqFinrank]

end AMSPhysical
#print axioms AMSPhysical.physicalTypeIRightBasis
