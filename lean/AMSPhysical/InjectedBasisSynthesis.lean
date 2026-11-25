import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical
variable {K V I X : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype I] [DecidableEq I]

def injectedBasisCoefficients (b : Module.Basis I K V) (e : I → X) : V →ₗ[K] X →₀ K :=
  (Finsupp.lmapDomain K K e).comp b.repr.toLinearMap

def injectedBasisSynthesis (b : Module.Basis I K V) (e : I → X) : (X →₀ K) →ₗ[K] V :=
  ∑ i : I,(LinearMap.toSpanSingleton K V (b i)).comp (Finsupp.lapply (e i))

theorem injectedBasisCoefficients_basis (b : Module.Basis I K V) (e : I → X) (i : I) :
    injectedBasisCoefficients b e (b i)=Finsupp.single (e i) 1 := by
  change Finsupp.mapDomain e (b.repr (b i))=_
  rw [Module.Basis.repr_self,Finsupp.mapDomain_single]

theorem injectedBasisSynthesis_single (b : Module.Basis I K V) (e : I → X) (he : Function.Injective e)
    (i : I) (a : K) : injectedBasisSynthesis b e (Finsupp.single (e i) a)=a • b i := by
  classical
  simp only [injectedBasisSynthesis,LinearMap.sum_apply,LinearMap.comp_apply,Finsupp.lapply_apply,
    LinearMap.toSpanSingleton_apply,Finsupp.single_apply,he.eq_iff]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    simp [hji,Ne.symm hji]
  · simp

theorem injectedBasisSynthesis_coefficients (b : Module.Basis I K V) (e : I → X) (he : Function.Injective e)
    (v : V) : injectedBasisSynthesis b e (injectedBasisCoefficients b e v)=v := by
  have hMaps : (injectedBasisSynthesis b e).comp (injectedBasisCoefficients b e)=LinearMap.id := by
    apply b.ext
    intro i
    simp only [LinearMap.comp_apply,injectedBasisCoefficients_basis,injectedBasisSynthesis_single b e he,one_smul,LinearMap.id_apply]
  exact DFunLike.congr_fun hMaps v

theorem injectedBasisCoefficients_synthesis (b : Module.Basis I K V) (e : I → X) (he : Function.Injective e)
    (f : X →₀ K) (hf : ∀ x,f x≠0 → ∃ i,e i=x) :
    injectedBasisCoefficients b e (injectedBasisSynthesis b e f)=f := by
  classical
  change injectedBasisCoefficients b e ((∑ i : I,(LinearMap.toSpanSingleton K V (b i)).comp (Finsupp.lapply (e i))) f)=_
  simp only [LinearMap.sum_apply,LinearMap.comp_apply,Finsupp.lapply_apply,LinearMap.toSpanSingleton_apply,
    map_sum,map_smul,injectedBasisCoefficients_basis,Finsupp.smul_single,smul_eq_mul,mul_one]
  apply Finsupp.ext
  intro x
  simp only [Finsupp.finset_sum_apply,Finsupp.single_apply]
  by_cases hx : ∃ i,e i=x
  · obtain ⟨i,rfl⟩ := hx
    simp only [he.eq_iff]
    simp
  · have hz : f x=0 := by by_contra h;exact hx (hf x h)
    have hn : ∀ i,e i≠x := fun i h =>hx ⟨i,h⟩
    simp only [if_neg (hn _),Finset.sum_const_zero,hz]

end AMSPhysical
