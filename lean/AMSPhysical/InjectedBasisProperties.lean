import InjectedBasisSynthesis

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
noncomputable section
namespace AMSPhysical
variable {K V I X : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype I] [DecidableEq I]

theorem injectedBasisCoefficients_injective (b : Module.Basis I K V) (e : I → X) (he : Function.Injective e) :
    Function.Injective (injectedBasisCoefficients b e) := by
  intro v w h
  have h0:=congrArg (injectedBasisSynthesis b e) h
  simpa only [injectedBasisSynthesis_coefficients b e he] using h0

theorem injectedBasisCoefficients_repr (b : Module.Basis I K V) (e : I → X) (he : Function.Injective e)
    (v : V) (i : I) : injectedBasisCoefficients b e v (e i)=b.repr v i :=
  Finsupp.mapDomain_apply he _ i

theorem injectedBasisCoefficients_support (b : Module.Basis I K V) (e : I → X)
    (v : V) (x : X) (hx : injectedBasisCoefficients b e v x≠0) : ∃ i,e i=x := by
  by_contra h
  exact hx (Finsupp.mapDomain_notin_range (b.repr v) x h)

end AMSPhysical
