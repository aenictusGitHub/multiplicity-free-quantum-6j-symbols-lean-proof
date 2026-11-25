import SaalschutzFiniteSum
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.ClusterPt

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
open Set Filter
open scoped Topology

theorem qPochhammer_prefix_ne_zero (Q a : ℝ) (n k : ℕ) (hn : qPochhammer Q a n≠0) (hk : k≤n) :
    qPochhammer Q a k≠0 := by
  apply qPochhammer_ne_zero
  intro j hj
  exact (Finset.prod_ne_zero_iff.mp hn) j (Finset.mem_range.mpr (lt_of_lt_of_le hj hk))

theorem saalschutzGeneric_dense (Q A B : ℝ) : Dense {C : ℝ | SaalschutzGeneric Q A B C} := by
  let bad : Set ℝ := ({0} ∪ Set.range (fun z : ℤ => Q^z)) ∪ Set.range (fun z : ℤ => A*B*Q^z)
  have hc : bad.Countable := ((Set.countable_singleton 0).union (Set.countable_range _)).union (Set.countable_range _)
  have hd := hc.dense_compl ℝ
  apply hd.mono
  intro C hC
  constructor
  · intro he
    apply hC
    exact Or.inl (Or.inl (Set.mem_singleton_iff.mpr he))
  · intro z he
    apply hC
    exact Or.inl (Or.inr ⟨z,he.symm⟩)
  · intro z he
    apply hC
    exact Or.inr ⟨z,he.symm⟩

theorem saalschutzTerm_continuousAt_C (Q A B C : ℝ) (n k : ℕ) (hC : C≠0)
    (hden : qPochhammer Q Q k*qPochhammer Q C k*qPochhammer Q (A*B*Q^(1-(n:ℤ))/C) k≠0) :
    ContinuousAt (fun c : ℝ => saalschutzTerm Q A B c n k) C := by
  have hD : ContinuousAt (fun c : ℝ => A*B*Q^(1-(n:ℤ))/c) C := continuousAt_const.div continuousAt_id hC
  have hP := (qPochhammer_continuous Q k).continuousAt.comp hD
  exact continuousAt_const.div
    ((continuousAt_const.mul (qPochhammer_continuous Q k).continuousAt).mul hP) hden

theorem saalschutzSum_continuousAt_C (Q A B C : ℝ) (hQ : 0<Q) (hQ1 : Q≠1) (n : ℕ)
    (hC : C≠0) (hCP : qPochhammer Q C n≠0)
    (hDP : qPochhammer Q (A*B*Q^(1-(n:ℤ))/C) n≠0) :
    ContinuousAt (fun c : ℝ => saalschutzSum Q A B c n) C := by
  unfold saalschutzSum
  apply tendsto_finset_sum (Finset.range (n+1))
  intro k hk
  have hkn : k≤n := by have hh := Finset.mem_range.mp hk;omega
  apply saalschutzTerm_continuousAt_C Q A B C n k hC
  exact mul_ne_zero
    (mul_ne_zero (qPochhammer_ne_zero Q Q k (fun j _ => baseQ_factor_nonzero Q hQ hQ1 j))
      (qPochhammer_prefix_ne_zero Q C n k hCP hkn))
    (qPochhammer_prefix_ne_zero Q _ n k hDP hkn)

theorem saalschutzProduct_continuousAt_C (Q A B C : ℝ) (n : ℕ)
    (hden : qPochhammer Q C n*qPochhammer Q (C/(A*B)) n≠0) :
    ContinuousAt (fun c : ℝ => saalschutzProduct Q A B c n) C := by
  have hA : ContinuousAt (fun c : ℝ => qPochhammer Q (c/A) n) C :=
    (qPochhammer_continuous Q n).continuousAt.comp (continuousAt_id.div_const A)
  have hB : ContinuousAt (fun c : ℝ => qPochhammer Q (c/B) n) C :=
    (qPochhammer_continuous Q n).continuousAt.comp (continuousAt_id.div_const B)
  have hAB : ContinuousAt (fun c : ℝ => qPochhammer Q (c/(A*B)) n) C :=
    (qPochhammer_continuous Q n).continuousAt.comp (continuousAt_id.div_const (A*B))
  exact (hA.mul hB).div ((qPochhammer_continuous Q n).continuousAt.mul hAB) hden

/-- Full admissible terminating q-Pfaff-Saalschutz identity, including integer-power parameters.
The generic-parameter restriction is removed by a proved density and continuity argument. -/
theorem qPfaffSaalschutz (Q A B C : ℝ) (hQ : 0<Q) (hQ1 : Q≠1)
    (hA : A≠0) (hB : B≠0) (hC : C≠0) (n : ℕ)
    (hCP : qPochhammer Q C n≠0) (hDP : qPochhammer Q (A*B*Q^(1-(n:ℤ))/C) n≠0)
    (hABP : qPochhammer Q (C/(A*B)) n≠0) :
    saalschutzSum Q A B C n=saalschutzProduct Q A B C n := by
  let good : Set ℝ := {c | SaalschutzGeneric Q A B c}
  have hd : Dense good := saalschutzGeneric_dense Q A B
  letI : NeBot (𝓝[good] C) := mem_closure_iff_nhdsWithin_neBot.mp (hd C)
  have hf : Tendsto (fun c => saalschutzSum Q A B c n) (𝓝[good] C) (𝓝 (saalschutzSum Q A B C n)) :=
    (saalschutzSum_continuousAt_C Q A B C hQ hQ1 n hC hCP hDP).tendsto.mono_left inf_le_left
  have hg : Tendsto (fun c => saalschutzProduct Q A B c n) (𝓝[good] C) (𝓝 (saalschutzProduct Q A B C n)) :=
    (saalschutzProduct_continuousAt_C Q A B C n (mul_ne_zero hCP hABP)).tendsto.mono_left inf_le_left
  have he : (fun c => saalschutzSum Q A B c n)=ᶠ[𝓝[good] C] (fun c => saalschutzProduct Q A B c n) := by
    filter_upwards [self_mem_nhdsWithin] with c hc
    exact qPfaffSaalschutz_generic Q A B c hQ hQ1 hA hB hc n
  exact tendsto_nhds_unique (Filter.Tendsto.congr' he hf) hg

/-- Denominator-cleared form: no nonvanishing hypothesis on (C/(AB);Q)_n.
This retains the cancellation information needed at boundary representation labels. -/
theorem qPfaffSaalschutz_cleared (Q A B C : ℝ) (hQ : 0<Q) (hQ1 : Q≠1)
    (hA : A≠0) (hB : B≠0) (hC : C≠0) (n : ℕ)
    (hCP : qPochhammer Q C n≠0) (hDP : qPochhammer Q (A*B*Q^(1-(n:ℤ))/C) n≠0) :
    saalschutzSum Q A B C n*qPochhammer Q C n*qPochhammer Q (C/(A*B)) n=
      qPochhammer Q (C/A) n*qPochhammer Q (C/B) n := by
  let good : Set ℝ := {c | SaalschutzGeneric Q A B c}
  have hd : Dense good := saalschutzGeneric_dense Q A B
  letI : NeBot (𝓝[good] C) := mem_closure_iff_nhdsWithin_neBot.mp (hd C)
  have hAB : ContinuousAt (fun c : ℝ => qPochhammer Q (c/(A*B)) n) C :=
    (qPochhammer_continuous Q n).continuousAt.comp (continuousAt_id.div_const (A*B))
  have hCA : ContinuousAt (fun c : ℝ => qPochhammer Q (c/A) n) C :=
    (qPochhammer_continuous Q n).continuousAt.comp (continuousAt_id.div_const A)
  have hCB : ContinuousAt (fun c : ℝ => qPochhammer Q (c/B) n) C :=
    (qPochhammer_continuous Q n).continuousAt.comp (continuousAt_id.div_const B)
  have hf := (((saalschutzSum_continuousAt_C Q A B C hQ hQ1 n hC hCP hDP).mul
    (qPochhammer_continuous Q n).continuousAt).mul hAB).tendsto.mono_left
    (show 𝓝[good] C≤𝓝 C from inf_le_left)
  have hg := (hCA.mul hCB).tendsto.mono_left (show 𝓝[good] C≤𝓝 C from inf_le_left)
  have he : (fun c => saalschutzSum Q A B c n*qPochhammer Q c n*qPochhammer Q (c/(A*B)) n)=ᶠ[𝓝[good] C]
      (fun c => qPochhammer Q (c/A) n*qPochhammer Q (c/B) n) := by
    filter_upwards [self_mem_nhdsWithin] with c hc
    have heq := qPfaffSaalschutz_generic Q A B c hQ hQ1 hA hB hc n
    have hden : qPochhammer Q c n*qPochhammer Q (c/(A*B)) n≠0 :=
      mul_ne_zero (qPochhammer_ne_zero _ _ n (fun k _ => hc.C_factor (ne_of_gt hQ) k))
        (qPochhammer_ne_zero _ _ n (fun k _ => hc.C_over_AB_factor (ne_of_gt hQ) hA hB k))
    unfold saalschutzProduct at heq
    simpa only [mul_assoc] using (eq_div_iff hden).mp heq
  exact tendsto_nhds_unique (Filter.Tendsto.congr' he hf) hg

end AMSPhysical

#print axioms AMSPhysical.qPfaffSaalschutz

#print axioms AMSPhysical.qPfaffSaalschutz_cleared
