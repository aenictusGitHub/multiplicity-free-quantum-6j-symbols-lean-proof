import QuantumTypeIILeftBasis
import QuantumTypeIIRightBasis
import OrthonormalChannelLine

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

theorem physicalTypeIILeftCoupling_unique_sign (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d)
    (v : physicalTypeIIHighestSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c d)
    (hv : v.val∈physicalTypeIILeftChannel q hq hq1 n hn a b c d r)
    (hvn : physicalTypeIITripleBilin q n a b c v.val v.val=1) :
    ∃ e : ℝ,(e=1 ∨ e= -1) ∧ v=e • physicalTypeIILeftCoupling q hq hq1 n hn a b c d hbal r := by
  let B:=restrictedBilinearPair (physicalTypeIITripleBilin q n a b c)
    (physicalTypeIIHighestSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c d)
  have hb (i j : TypeIICommonIndex a b c d) :
      B (physicalTypeIILeftBasis q hq hq1 n hn a b c d hbal i)
        (physicalTypeIILeftBasis q hq hq1 n hn a b c d hbal j)=if i=j then 1 else 0 := by
    rw [physicalTypeIILeftBasis_apply,physicalTypeIILeftBasis_apply]
    exact physicalTypeIILeftCoupling_pair q hq hq1 n hn a b c d hbal i j
  obtain ⟨e,he,hv'⟩:=unit_vector_on_orthonormal_channel_line B
    (physicalTypeIILeftBasis q hq hq1 n hn a b c d hbal) hb r v (fun j hj =>by
      rw [physicalTypeIILeftBasis_apply]
      exact physicalTypeIILeftChannels_orthogonal q hq hq1 n hn a b c d j r hj _ _
        (physicalTypeIILeftCoupling_mem q hq hq1 n hn a b c d hbal j) hv) hvn
  exact ⟨e,he,by rwa [physicalTypeIILeftBasis_apply] at hv'⟩

theorem physicalTypeIIRightCoupling_unique_sign (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c d : ℕ) (hbal : a+b=c+d) (t : QuantumCupIndex a c b)
    (v : physicalTypeIIHighestSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c d)
    (hv : v.val∈physicalTypeIIRightChannel q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c t)
    (hvn : physicalTypeIITripleBilin q n a b c v.val v.val=1) :
    ∃ e : ℝ,(e=1 ∨ e= -1) ∧ v=e • physicalTypeIIRightCoupling q hq hq1 n hn a b c d hbal t := by
  let E:=physicalTypeIIToCompleteI q hq hq1 n hn a b c d hbal
  have hm:= (physicalTypeIIToCompleteI_right_mem_iff q hq hq1 n hn a b c d hbal t v).mpr hv
  have hN : physicalTripleBilin q n a c b (E v).val (E v).val=1 :=
    (physicalTypeIIToCompleteI_isometry q hq hq1 n hn a b c d hbal v v).trans hvn
  obtain ⟨e,he,hV⟩:=physicalTypeIRightCoupling_unique_sign q hq hq1 n hn a c 0 b (by omega) (Or.inl rfl) t (E v) hm hN
  refine ⟨e,he,?_⟩
  apply E.injective
  change E v=E (e • E.symm (physicalTypeIRightCoupling q hq hq1 n hn a c 0 b (by omega) (Or.inl rfl) t))
  rw [map_smul,LinearEquiv.apply_symm_apply]
  exact hV

end AMSPhysical
#print axioms AMSPhysical.physicalTypeIILeftCoupling_unique_sign
#print axioms AMSPhysical.physicalTypeIIRightCoupling_unique_sign
