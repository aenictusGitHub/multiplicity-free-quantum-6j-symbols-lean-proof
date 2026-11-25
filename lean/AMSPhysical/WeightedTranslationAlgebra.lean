import WeightedTranslation

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
variable {K X : Type*} [Field K] [AddCommGroup X]

theorem weightedTranslation_mul (s t : X) (w v : X → K) :
    weightedTranslation s w*weightedTranslation t v=
      weightedTranslation (s+t) (fun x =>v x*w (x+t)) := by
  apply Finsupp.lhom_ext
  intro x a
  simp only [Module.End.mul_apply,weightedTranslation_single]
  have he : x+t+s=x+(s+t) := by abel
  rw [he]
  congr 1
  ring

theorem weightedTranslation_sub (s : X) (w v : X → K) :
    weightedTranslation s w-weightedTranslation s v=weightedTranslation s (fun x =>w x-v x) := by
  apply Finsupp.lhom_ext
  intro x a
  simp only [LinearMap.sub_apply,weightedTranslation_single,← Finsupp.single_sub]
  congr 1
  ring

theorem weightedTranslation_commutator (s t : X) (w v : X → K) :
    weightedTranslation s w*weightedTranslation t v-weightedTranslation t v*weightedTranslation s w=
      weightedTranslation (s+t) (fun x =>v x*w (x+t)-w x*v (x+s)) := by
  rw [weightedTranslation_mul,weightedTranslation_mul,add_comm t s,weightedTranslation_sub]

theorem weightedTranslation_zero (s : X) : weightedTranslation s (fun _ => (0:K))=0 := by
  apply Finsupp.lhom_ext
  intro x a
  simp

end AMSPhysical
