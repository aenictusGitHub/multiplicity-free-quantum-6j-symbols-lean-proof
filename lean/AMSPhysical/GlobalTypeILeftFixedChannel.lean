import GlobalTypeILeftStep
import GlobalMixedPairTransfers

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def globalTypeILeftCupIndex (p s c r : ℕ) (hs : s≤c) : QuantumCupIndex (p+r) (s+r) c :=
  ⟨⟨r,by omega⟩,by change r≤p+r ∧ s+r-r≤c;omega⟩

def globalTypeILeftVector (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h p s c r : ℕ) (hs : s≤c) :=
  physicalTypeILeftCoupling q hq hq1 (h+1) (by omega) (p+r) (s+r) 0 c (by omega) (Or.inl rfl)
    (globalTypeILeftCupIndex p s c r hs)

def globalTypeILeftUnassoc (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h p s c r : ℕ) (hs : s≤c) :=
  (TensorProduct.assoc ℝ _ _ _).symm (globalTypeILeftVector q hq hq1 h p s c r hs).val

theorem globalTypeILeftCupIndex_pair (p s c r : ℕ) (hs : s≤c) :
    physicalTypeILeftIndex (p+r) (s+r) 0 c (globalTypeILeftCupIndex p s c r hs) =
      globalMixedPairIndex p s r := by
  apply Fin.ext
  rfl

theorem globalTypeILeftUnassoc_mem (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h p s c r : ℕ) (hs : s≤c) :
    globalTypeILeftUnassoc q hq hq1 h p s c r hs ∈
      LinearMap.range (TensorProduct.map
        (globalMixedPairRealization q hq hq1 (h+1) (by omega) p s r).channel.subtype
        (LinearMap.id : quantumOccupationSpace ℝ (Fin (h+2)) c →ₗ[ℝ] _)) := by
  have hv:=physicalTypeILeftCoupling_mem_channel q hq hq1 (h+1) (by omega) (p+r) (s+r) 0 c
    (by omega) (Or.inl rfl) (globalTypeILeftCupIndex p s c r hs)
  change (globalTypeILeftVector q hq hq1 h p s c r hs).val ∈
    physicalTripleLeftChannelGeneral q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      (h+1) (p+r) (s+r) c _ at hv
  rw [physicalTripleLeftChannelGeneral_actual q hq hq1 (h+1) (by omega)] at hv
  obtain ⟨w,hw,he⟩:=hv
  have hw' : globalTypeILeftUnassoc q hq hq1 h p s c r hs=w := by
    change (TensorProduct.assoc ℝ _ _ _).symm _ = _
    rw [← he]
    exact LinearEquiv.symm_apply_apply _ w
  rw [hw']
  let S:=mixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1)
    (p+r) (s+r) (physicalTypeILeftIndex (p+r) (s+r) 0 c (globalTypeILeftCupIndex p s c r hs))
  let T:=(globalMixedPairRealization q hq hq1 (h+1) (by omega) p s r).channel
  have hST : S=T := by
    dsimp only [S,T]
    rw [globalTypeILeftCupIndex_pair,globalMixedPairRealization_channel]
  have he':=tensorLeft_range_congr (A:=quantumOccupationSpace ℝ (Fin (h+2)) c) S T hST
  change w∈LinearMap.range (TensorProduct.map S.subtype LinearMap.id) at hw
  rw [he'] at hw
  exact hw

theorem globalTypeILeftVector_creation (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h p s c r : ℕ) (hs : s≤c) :
    finiteTripleLeftCreation q (h+1) (p+r) (s+r) c
      (globalTypeILeftVector q hq hq1 h p s c r hs).val =
      ((-1:ℝ)^h*mixedCreationUnitScale q (h+1) (p+r) (s+r) (globalMixedPairIndex p s r)) •
        (globalTypeILeftVector q hq hq1 h p s c (r+1) hs).val := by
  have he:=physicalTypeILeftCoupling_creation q hq hq1 (h+1) (by omega) (p+r) (s+r) c
    (by omega) (globalTypeILeftCupIndex p s c r hs)
  rw [typeILeftCreationScale,globalTypeILeftCupIndex_pair,← mixedCreationUnitScale_eq_sqrt q hq] at he
  exact he

theorem globalTypeILeftUnassoc_step_transfer (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h p s c r : ℕ) (hs : s≤c) :
    globalTypeILeftUnassoc q hq hq1 h p s c (r+1) hs =
      (-1:ℝ)^h • TensorProduct.map
        (globalMixedPairTransfer q hq hq1 (h+1) (by omega) p s r (r+1))
        (LinearMap.id : quantumOccupationSpace ℝ (Fin (h+2)) c →ₗ[ℝ] _)
        (globalTypeILeftUnassoc q hq hq1 h p s c r hs) := by
  have hc:=tensorLeft_equal_on_channel
    (globalMixedPairRealization q hq hq1 (h+1) (by omega) p s r).channel
    (mixedFiniteCreation q (h+1) (p+r) (s+r))
    (globalMixedPairTransfer q hq hq1 (h+1) (by omega) p s r (r+1))
    (mixedCreationUnitScale q (h+1) (p+r) (s+r) (globalMixedPairIndex p s r))
    (fun x hx=>globalMixedPair_creation_transfer q hq hq1 (h+1) (by omega) p s r ⟨x,hx⟩)
    (globalTypeILeftUnassoc q hq hq1 h p s c r hs)
    (globalTypeILeftUnassoc_mem q hq hq1 h p s c r hs)
  have hn:=congrArg (fun v=>(TensorProduct.assoc ℝ
    (quantumOccupationSpace ℝ (Fin ((h+1)+1)) ((p+r)+1))
    (quantumOccupationSpace ℝ (Fin ((h+1)+1)) ((s+r)+1))
    (quantumOccupationSpace ℝ (Fin ((h+1)+1)) c)).symm v)
      (globalTypeILeftVector_creation q hq hq1 h p s c r hs)
  rw [finiteTripleLeftCreation_tensor] at hn
  simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply,map_smul] at hn
  change TensorProduct.map (mixedFiniteCreation q (h+1) (p+r) (s+r)) LinearMap.id
    (globalTypeILeftUnassoc q hq hq1 h p s c r hs) =
      ((-1:ℝ)^h*mixedCreationUnitScale q (h+1) (p+r) (s+r) (globalMixedPairIndex p s r)) •
        globalTypeILeftUnassoc q hq hq1 h p s c (r+1) hs at hn
  rw [hc] at hn
  have he : TensorProduct.map
      (globalMixedPairTransfer q hq hq1 (h+1) (by omega) p s r (r+1)) LinearMap.id
      (globalTypeILeftUnassoc q hq hq1 h p s c r hs) =
      (-1:ℝ)^h • globalTypeILeftUnassoc q hq hq1 h p s c (r+1) hs := by
    apply smul_right_injective _ (ne_of_gt (mixedCreationUnitScale_pos q hq (h+1) (p+r) (s+r)
      (globalMixedPairIndex p s r)))
    simpa only [smul_smul,mul_comm] using hn
  rw [he,smul_smul,← mul_pow]
  norm_num

/-- A fixed left outer vertex suffices for every forward mixed realization.
The only extra sign is the explicit intrinsic mixed-vertex sign. -/
theorem globalTypeILeftUnassoc_from_zero (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h p s c r : ℕ) (hs : s≤c) :
    globalTypeILeftUnassoc q hq hq1 h p s c r hs =
      (-1:ℝ)^(h*r) • TensorProduct.map
        (globalMixedPairTransfer q hq hq1 (h+1) (by omega) p s 0 r)
        (LinearMap.id : quantumOccupationSpace ℝ (Fin (h+2)) c →ₗ[ℝ] _)
        (globalTypeILeftUnassoc q hq hq1 h p s c 0 hs) := by
  induction r with
  | zero =>
    simp only [Nat.mul_zero,pow_zero,one_smul]
    symm
    exact tensorLeft_identity_on_channel
      (globalMixedPairRealization q hq hq1 (h+1) (by omega) p s 0).channel
      (globalMixedPairTransfer q hq hq1 (h+1) (by omega) p s 0 0)
      (fun x hx=>globalMixedPairTransfer_self_on_channel q hq hq1 (h+1) (by omega) p s 0 ⟨x,hx⟩)
      _ (globalTypeILeftUnassoc_mem q hq hq1 h p s c 0 hs)
  | succ r ih =>
    rw [globalTypeILeftUnassoc_step_transfer,ih,map_smul,smul_smul,tensorLeft_map_comp,
      globalMixedPairTransfer_comp]
    simp only [Nat.mul_add,Nat.mul_one,pow_add]
    rw [mul_comm]

end AMSPhysical
#print axioms AMSPhysical.globalTypeILeftUnassoc_from_zero
