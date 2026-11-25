import PhysicalTypeIChannelCouplings

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical

/-- Physical Type-I rank reduction for ANY independently chosen normalized
actual channel highest vectors. The signs are chosen separately for each
channel, so the conclusion is genuine row/column phase equivalence. -/
theorem physicalTypeIrecoupling_rankReduction (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l m h c : ℕ) (hadm : m≤l+c) (hRank : h=0 ∨ n=1)
    (u v : QuantumCupIndex l m c → physicalQuantumHighestMultiplicity q (ne_of_gt hq)
      (qInteger_denominator_ne_zero q hq hq1) n l m h c)
    (hu : ∀ t,u t∈physicalTypeILeftChannelSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m h c t)
    (hv : ∀ t,v t∈physicalTypeIRightChannelSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m h c t)
    (hun : ∀ t,physicalTripleBilin q n l (m+h) c (u t).val (u t).val=1)
    (hvn : ∀ t,physicalTripleBilin q n l (m+h) c (v t).val (v t).val=1) :
    ∃ eps eta : QuantumCupIndex l m c → ℝ,
      (∀ t,eps t=1 ∨ eps t= -1) ∧ (∀ t,eta t=1 ∨ eta t= -1) ∧
      ∀ s t,physicalTripleBilin q n l (m+h) c (u s).val (v t).val=
        eps s*eta t*quantumRacahMatrix q hq hq1 l (m+(h+n-1)) c
          (quantumCupLeftPath l m (h+n-1) c s) (quantumCupRightPath l m (h+n-1) c t) := by
  choose eps heps hU using fun t =>physicalTypeILeftCoupling_unique_sign q hq hq1 n hn l m h c hadm hRank t (u t) (hu t) (hun t)
  choose eta heta hV using fun t =>physicalTypeIRightCoupling_unique_sign q hq hq1 n hn l m h c hadm hRank t (v t) (hv t) (hvn t)
  refine ⟨eps,eta,heps,heta,?_⟩
  intro s t
  rw [hU s,hV t]
  simp only [Submodule.coe_smul_of_tower,map_smul,LinearMap.smul_apply,smul_eq_mul]
  rw [physicalTypeICoupling_overlap_rankTwo q hq hq1 n hn l m h c hadm hRank]
  ring

end AMSPhysical
#print axioms AMSPhysical.physicalTypeIrecoupling_rankReduction
