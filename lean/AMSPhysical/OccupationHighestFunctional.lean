import QuantumTripleHighestBase
import QuantumCreationBoundary
import TensorHighestFunctional

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

def occupationHighestFunctional (n p : ℕ) : quantumOccupationSpace ℝ (Fin (n+1)) p →ₗ[ℝ] ℝ :=
  (Finsupp.lapply (highestOccupation n p).val).comp (quantumOccupationSpace ℝ (Fin (n+1)) p).subtype

theorem occupationHighestFunctional_highest (n p : ℕ) :
    occupationHighestFunctional n p (quantumOccupationBasis (K:=ℝ) p (highestOccupation n p))=1 := by
  simp [occupationHighestFunctional,quantumOccupationBasis_coe]

theorem occupationHighestFunctional_F (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (n p : ℕ) (i : Fin n) (v : quantumOccupationSpace ℝ (Fin (n+1)) p) :
    occupationHighestFunctional n p (typeAFiniteGenerator q hq hD n p i 1 v)=0 := by
  change (typeAFiniteGenerator q hq hD n p i 1 v).val (highestOccupation n p).val=0
  rw [typeAFiniteGenerator_coe]
  change weightedTranslation (latticeRoot i.succ i.castSucc)
    (fun x : Fin (n+1) → ℤ => qInteger q (x i.castSucc)) v.val (highestOccupation n p).val=0
  rw [weightedTranslation_apply]
  have hi : i.succ≠(0:Fin (n+1)) := by intro he;have h:=congrArg Fin.val he;simp at h
  have hneg : ((highestOccupation n p).val-latticeRoot i.succ i.castSucc) i.succ= -1 := by
    simp only [Pi.sub_apply,latticeRoot_target _ _ (Ne.symm (typeA_root_endpoints n i)),highestOccupation,
      Pi.single_apply,if_neg hi,if_neg (Ne.symm hi)]
    ring
  have hz : v.val ((highestOccupation n p).val-latticeRoot i.succ i.castSucc)=0 := by
    by_contra hc
    have hs : (highestOccupation n p).val-latticeRoot i.succ i.castSucc∈occupationWeights (Fin (n+1)) p :=
      v.property (Finsupp.mem_support_iff.mpr hc)
    have hn:=hs.1 i.succ
    rw [hneg] at hn
    omega
  rw [hz,zero_mul]

theorem occupationHighestFunctional_Ki (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (n p : ℕ) (i : Fin n) (v : quantumOccupationSpace ℝ (Fin (n+1)) p) :
    occupationHighestFunctional n p (typeAFiniteGenerator q hq hD n p i 3 v) =
      q^(-(p:ℤ)*(if i.castSucc=0 then 1 else 0))*occupationHighestFunctional n p v := by
  change (typeAFiniteGenerator q hq hD n p i 3 v).val (highestOccupation n p).val = _
  rw [typeAFiniteGenerator_coe]
  change weightedTranslation (0 : Fin (n+1) → ℤ)
    (fun x => q^(latticePairing (-typeARoot n i) x)) v.val (highestOccupation n p).val = _
  rw [weightedTranslation_apply,sub_zero]
  have he : latticePairing (-typeARoot n i) (highestOccupation n p).val =
      -(p:ℤ)*(if i.castSucc=0 then 1 else 0) := by
    change latticePairing (-latticeRoot i.castSucc i.succ) (highestOccupation n p).val = _
    simp only [latticePairing,Pi.neg_apply,neg_mul,Finset.sum_neg_distrib]
    change -latticePairing (latticeRoot i.castSucc i.succ) (highestOccupation n p).val = _
    rw [latticePairing_root_left]
    change -simpleOccupationWeight n (highestOccupation n p).val i=_
    rw [simpleOccupationWeight_highest]
  rw [he]
  exact mul_comm _ _

end AMSPhysical
#print axioms AMSPhysical.occupationHighestFunctional_F
#print axioms AMSPhysical.occupationHighestFunctional_Ki
