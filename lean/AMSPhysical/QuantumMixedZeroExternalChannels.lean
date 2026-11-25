import QuantumReverseFusion
import QuantumPhysicalTripleInstances

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
noncomputable section
namespace AMSPhysical

theorem mixedFusionChannel_zero_left_top (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (m : ℕ) (r : MixedFusionIndex 0 m) :
    mixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n 0 m r=⊤ := by
  have ht:=mixedFusionSpan_eq_top q hq hq1 n hn 0 m
  change (⨆ s : MixedFusionIndex 0 m,mixedFusionChannelAt q (ne_of_gt hq)
    (qInteger_denominator_ne_zero q hq hq1) n 0 m s)=⊤ at ht
  have hc (s : MixedFusionIndex 0 m) : s=r := by
    apply Fin.ext
    have hs:=s.isLt
    have hr:=r.isLt
    omega
  letI : Nonempty (MixedFusionIndex 0 m):=⟨r⟩
  simpa only [hc,iSup_const] using ht

theorem mixedFusionChannel_zero_right_top (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l : ℕ) (r : MixedFusionIndex l 0) :
    mixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l 0 r=⊤ := by
  have ht:=mixedFusionSpan_eq_top q hq hq1 n hn l 0
  change (⨆ s : MixedFusionIndex l 0,mixedFusionChannelAt q (ne_of_gt hq)
    (qInteger_denominator_ne_zero q hq hq1) n l 0 s)=⊤ at ht
  have hc (s : MixedFusionIndex l 0) : s=r := by
    apply Fin.ext
    have hs:=s.isLt
    have hr:=r.isLt
    omega
  letI : Nonempty (MixedFusionIndex l 0):=⟨r⟩
  simpa only [hc,iSup_const] using ht

theorem reverseMixedFusionChannel_zero_left_top (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (m : ℕ) (r : MixedFusionIndex 0 m) :
    reverseMixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n 0 m r=⊤ := by
  rw [← reverseMixedFusionChannelAt_map,mixedFusionChannel_zero_left_top q hq hq1 n hn,Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (mixedReflection n 0 m).surjective

theorem reverseMixedFusionChannel_zero_right_top (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l : ℕ) (r : MixedFusionIndex l 0) :
    reverseMixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l 0 r=⊤ := by
  rw [← reverseMixedFusionChannelAt_map,mixedFusionChannel_zero_right_top q hq hq1 n hn,Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (mixedReflection n l 0).surjective

end AMSPhysical
#print axioms AMSPhysical.mixedFusionChannel_zero_left_top
#print axioms AMSPhysical.reverseMixedFusionChannel_zero_right_top
