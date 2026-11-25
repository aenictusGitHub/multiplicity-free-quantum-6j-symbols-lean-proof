import QuantumLattice

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
noncomputable section
namespace AMSPhysical
variable {K X : Type*} [Field K] [AddCommGroup X]

/-- A weighted translation on an actual finitely supported coefficient space. -/
def weightedTranslation (s : X) (w : X → K) : Module.End K (X →₀ K) :=
  Finsupp.lsum K (fun x => LinearMap.toSpanSingleton K _ (Finsupp.single (x+s) (w x)))

@[simp] theorem weightedTranslation_single (s : X) (w : X → K) (x : X) (a : K) :
    weightedTranslation s w (Finsupp.single x a)=Finsupp.single (x+s) (a*w x) := by
  unfold weightedTranslation
  rw [Finsupp.lsum_single]
  simp only [LinearMap.toSpanSingleton_apply,Finsupp.smul_single,smul_eq_mul]

theorem weightedTranslation_apply (s : X) (w : X → K) (f : X →₀ K) (x : X) :
    weightedTranslation s w f x=f (x-s)*w (x-s) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add,Finsupp.add_apply,hf,hg,add_mul]
  | single y a =>
    rw [weightedTranslation_single]
    by_cases h : y+s=x
    · have hy : y=x-s := (eq_sub_iff_add_eq).mpr h
      rw [h,hy]
      simp
    · have hy : y≠x-s := by intro he;apply h;exact (eq_sub_iff_add_eq.mp he)
      simp only [Finsupp.single_apply,if_neg h,if_neg hy,zero_mul]

end AMSPhysical
