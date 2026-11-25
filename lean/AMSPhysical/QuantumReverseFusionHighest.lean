import QuantumReverseFusion
import QuantumMixedFusionNorm

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 180000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem mixedHighestDynkin_rev (n a b : ℕ) (i : Fin n) :
    mixedHighestDynkin n a b i.rev=mixedHighestDynkin n b a i := by
  have h0 : i.rev.castSucc=(0:Fin (n+1)) ↔ i.succ=Fin.last n := by
    simp only [Fin.ext_iff,Fin.coe_castSucc,Fin.val_rev,Fin.val_zero,Fin.val_succ,Fin.val_last]
    omega
  have hn : i.rev.succ=Fin.last n ↔ i.castSucc=(0:Fin (n+1)) := by
    simp only [Fin.ext_iff,Fin.val_succ,Fin.val_rev,Fin.val_last,Fin.coe_castSucc,Fin.val_zero]
    omega
  simp only [mixedHighestDynkin,h0,hn]
  ring

theorem reverseMixedFusionHighestAt_E_zero (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n l m : ℕ)
    (r : MixedFusionIndex l m) (i : Fin n) :
    typeAReverseMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m
      (typeAAlgebraGenerator q n i 0) (reverseMixedFusionHighestAt q n l m r)=0 := by
  have h:=mixedReflection_intertwines q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
    n l m (typeAAlgebraGenerator q n i.rev 0) (mixedFusionHighestAt q n l m r)
  rw [typeADynkinReflection_generator,Fin.rev_rev,mixedFusionHighestAt_E_zero q hq hq1,map_zero] at h
  exact h.symm

theorem reverseMixedFusionHighestAt_K (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n l m : ℕ)
    (r : MixedFusionIndex l m) (i : Fin n) :
    typeAReverseMixedTensor q hq hD n l m (typeAAlgebraGenerator q n i 2)
      (reverseMixedFusionHighestAt q n l m r)=
      q^(mixedHighestDynkin n (m-r.val) (l-r.val) i) • reverseMixedFusionHighestAt q n l m r := by
  have h:=mixedReflection_intertwines q hq hD n l m (typeAAlgebraGenerator q n i.rev 2)
    (mixedFusionHighestAt q n l m r)
  rw [typeADynkinReflection_generator,Fin.rev_rev,mixedFusionHighestAt_K,map_smul,mixedHighestDynkin_rev] at h
  exact h.symm

theorem reverseMixedFusionHighestAt_norm (q : ℝ) (hq : 0<q) (n : ℕ) (hn : 0<n) (l m : ℕ)
    (r : MixedFusionIndex l m) :
    reverseMixedTensorBilin q n l m (reverseMixedFusionHighestAt q n l m r) (reverseMixedFusionHighestAt q n l m r)=
      mixedCouplingNormClosed q n (l-r.val) (m-r.val) r.val := by
  rw [reverseMixedFusionHighestAt,mixedReflection_isometry q (ne_of_gt hq)]
  exact mixedFusionHighestAt_norm_closed q hq n hn l m r

end AMSPhysical
