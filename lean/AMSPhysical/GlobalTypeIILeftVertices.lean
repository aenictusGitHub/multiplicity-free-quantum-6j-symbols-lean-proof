import GlobalHighestCarrierCoherence
import GlobalVertexBending
import QuantumTypeIIHighestBoundary
import QuantumTypeIILeftNormClosed
import PhysicalTypeIICalibratedGauge

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

/-- A fixed two-row carrier, independent of either exterior pair. -/
def globalTwoRowCarrier (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (S r : ℕ) (hr : 2*r≤S) :=
  twoRowHighestRealization q hq hq1 n hn S r (S-r) r (by omega) (by omega) (le_refl r)

/-- One vertex for the ordered triple (S_l,S_m;T_{S-2r,r}). -/
def globalTwoRowIn (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (S r : ℕ) (hr : 2*r≤S) (l m : ℕ) (hS : l+m=S) (hl : r≤l) (hm : r≤m) :=
  (twoRowHighestRealization q hq hq1 n hn S r l m hS hl hm).channel.subtype.comp
    ((globalTwoRowCarrier q hq hq1 n hn S r hr).transport (ne_of_gt hq)
      (twoRowHighestRealization q hq hq1 n hn S r l m hS hl hm)).toLinearMap

/-- The adjoint-direction vertex, determined by (S_d,S_c;T). -/
def globalTwoRowOut (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (S r : ℕ) (hr : 2*r≤S) (d c : ℕ) (hS : d+c=S) (hd : r≤d) (hc : r≤c) :=
  ((twoRowHighestRealization q hq hq1 n hn S r d c hS hd hc).transport (ne_of_gt hq)
    (globalTwoRowCarrier q hq hq1 n hn S r hr)).toLinearMap.comp
      (twoRowHighestRealization q hq hq1 n hn S r d c hS hd hc).channelProjection

theorem physicalTypeIILeftPairMap_global_factor (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (a b c d : ℕ) (hbal : a+b=c+d)
    (r : TypeIICommonIndex a b c d) :
    physicalTypeIILeftPairMap q hq hq1 n hn a b c d hbal r =
      (globalTwoRowIn q hq hq1 n hn (a+b) r.val (by have hr:=r.isLt;omega)
        a b rfl (by have hr:=r.isLt;omega) (by have hr:=r.isLt;omega)).comp
      (globalTwoRowOut q hq hq1 n hn (a+b) r.val (by have hr:=r.isLt;omega)
        d c (by omega) (by have hr:=r.isLt;omega) (by have hr:=r.isLt;omega)) := by
  exact CompactHighestRealization.channelTransfer_factor (ne_of_gt hq)
    (typeIILeftSource q hq hq1 n hn a b c d hbal r)
    (typeIILeftTarget q hq hq1 n hn a b c d r)
    (globalTwoRowCarrier q hq hq1 n hn (a+b) r.val (by have hr:=r.isLt;omega))

/-- The complete raw Type-II tree is a composition of vertices depending
only on their incident representations. There is no exterior-quadruple phase. -/
theorem physicalTypeIILeftTreeMap_global_factor (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (a b c d : ℕ) (hbal : a+b=c+d)
    (r : TypeIICommonIndex a b c d) :
    physicalTypeIILeftTreeMap q hq hq1 n hn a b c d hbal r =
      (TensorProduct.assoc ℝ _ _ _).toLinearMap.comp
        ((TensorProduct.map
          (globalTwoRowIn q hq hq1 n hn (a+b) r.val (by have hr:=r.isLt;omega)
            a b rfl (by have hr:=r.isLt;omega) (by have hr:=r.isLt;omega))
          (LinearMap.id : quantumOccupationSpace ℝ (Fin (n+1)) c →ₗ[ℝ] _)).comp
        (bendRight
          (globalTwoRowOut q hq hq1 n hn (a+b) r.val (by have hr:=r.isLt;omega)
            d c (by omega) (by have hr:=r.isLt;omega) (by have hr:=r.isLt;omega))
          (symmetricCoevaluation q n c))) := by
  rw [physicalTypeIILeftTreeMap_eq_bend, physicalTypeIILeftPairMap_global_factor,
    bendRight_postcompose]

/-- The calibrated left normalization and sign are functions of the second
vertex alone: the internal two-row label, the opposite degree and the output. -/
def globalTypeIILeftVertexScale (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (S r d : ℕ) : ℝ :=
  (-1:ℝ)^r * (Real.sqrt
    (twoRowIrrepQuantumDimension q hq hq1 n hn (S-2*r) r / symmetricQuantumDimension q n d))⁻¹

theorem physicalTypeIICalibratedLeft_global_scale (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d) :
    (physicalTypeIICalibratedLeft q hq hq1 h a b c d hbal r).val =
      globalTypeIILeftVertexScale q hq hq1 (h+1) (by omega) (c+d) r.val d •
        (physicalTypeIILeftHighest q hq hq1 (h+1) (by omega) a b c d hbal r).val := by
  unfold physicalTypeIICalibratedLeft physicalTypeIILeftCoupling
  simp only [Submodule.coe_smul_of_tower, smul_smul]
  rw [physicalTypeIILeftHighestNormSq_closed]
  have he : (a-r.val)+(b-r.val)=c+d-2*r.val := by have hr:=r.isLt;omega
  rw [he]
  rfl

end AMSPhysical
#print axioms AMSPhysical.physicalTypeIILeftTreeMap_global_factor
#print axioms AMSPhysical.physicalTypeIICalibratedLeft_global_scale
