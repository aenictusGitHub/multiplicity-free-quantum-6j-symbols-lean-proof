import WeightedTranslationAlgebra

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
variable {K X : Type*} [Field K] [AddCommGroup X]

theorem weightedTranslation_smul (a : K) (s : X) (w : X → K) :
    a • weightedTranslation s w=weightedTranslation s (fun x =>a*w x) := by
  apply Finsupp.lhom_ext
  intro x c
  simp only [LinearMap.smul_apply,weightedTranslation_single,Finsupp.smul_single,smul_eq_mul]
  congr 1
  ring

theorem weightedTranslation_qcommutator (a : K) (s t : X) (w v : X → K) :
    weightedTranslation s w*weightedTranslation t v-a • (weightedTranslation t v*weightedTranslation s w)=
      weightedTranslation (s+t) (fun x =>v x*w (x+t)-a*w x*v (x+s)) := by
  rw [weightedTranslation_mul,weightedTranslation_mul,add_comm t s,weightedTranslation_smul,weightedTranslation_sub]
  congr 1
  funext x
  ring

theorem weightedTranslation_sum {I : Type*} [Fintype I] (s : X) (w : I → X → K) :
    (∑ i : I,weightedTranslation s (w i))=weightedTranslation s (fun x =>∑ i : I,w i x) := by
  classical
  apply Finsupp.lhom_ext
  intro x a
  simp only [LinearMap.sum_apply,weightedTranslation_single]
  apply Finsupp.ext
  intro y
  simp only [Finsupp.finset_sum_apply,Finsupp.single_apply]
  split_ifs <;> simp [Finset.mul_sum]

end AMSPhysical
