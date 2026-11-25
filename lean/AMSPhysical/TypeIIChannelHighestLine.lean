import QuantumTypeIIChannelGauge
import NativeInnerHighestLines

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem submodule_finrank_one_of_spanning (S : Submodule ℝ V) (v : V) (hv : v∈S) (hn : v≠0)
    (hSpan : ∀ w∈S,∃ a : ℝ,w=a • v) : Module.finrank ℝ S=1 := by
  have he : S=Submodule.span ℝ {v} := by
    apply le_antisymm
    · intro w hw
      obtain ⟨a,rfl⟩:=hSpan w hw
      exact Submodule.smul_mem _ a (Submodule.subset_span (Set.mem_singleton v))
    · exact Submodule.span_le.mpr (by intro w hw;rcases Set.mem_singleton_iff.mp hw with rfl;exact hv)
  rw [he]
  exact finrank_span_singleton hn

def physicalTypeIILeftHighestLine (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c d : ℕ) (r : TypeIICommonIndex a b c d) :=
  Submodule.comap
    (physicalTypeIIHighestSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c d).subtype
    (physicalTypeIILeftChannel q hq hq1 n hn a b c d r)

theorem physicalTypeIILeftHighestLine_finrank (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d) :
    Module.finrank ℝ (physicalTypeIILeftHighestLine q hq hq1 n hn a b c d r)=1 := by
  let V : Type:=physicalTypeIIHighestSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c d
  letI : AddCommGroup V:=inferInstance
  letI : Module ℝ V:=inferInstance
  let B:=restrictedBilinearPair (physicalTypeIITripleBilin q n a b c)
    (physicalTypeIIHighestSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c d)
  let b0:=physicalTypeIILeftBasis q hq hq1 n hn a b c d hbal
  have hb : ∀ i j,B (b0 i) (b0 j)=if i=j then 1 else 0 := by
    intro i j
    rw [physicalTypeIILeftBasis_apply,physicalTypeIILeftBasis_apply]
    exact physicalTypeIILeftCoupling_pair q hq hq1 n hn a b c d hbal i j
  apply submodule_finrank_one_of_spanning _ (b0 r)
  · change (b0 r).val∈physicalTypeIILeftChannel q hq hq1 n hn a b c d r
    rw [physicalTypeIILeftBasis_apply]
    exact physicalTypeIILeftCoupling_mem q hq hq1 n hn a b c d hbal r
  · exact b0.ne_zero r
  · intro v hv
    have hCoeff : ∀ j,j≠r → b0.repr v j=0 := by
      intro j hj
      rw [← orthonormal_basis_coord_right B b0 hb j v,physicalTypeIILeftBasis_apply]
      exact physicalTypeIILeftChannels_orthogonal q hq hq1 n hn a b c d j r hj _ _
        (physicalTypeIILeftCoupling_mem q hq hq1 n hn a b c d hbal j) hv
    refine ⟨b0.repr v r,?_⟩
    calc
      v = ∑ j,b0.repr v j • b0 j := (b0.sum_repr v).symm
      _ = _ := by
        apply Finset.sum_eq_single r
        · intro j hj hjr;rw [hCoeff j hjr,zero_smul]
        · simp

end AMSPhysical
#print axioms AMSPhysical.physicalTypeIILeftHighestLine_finrank
