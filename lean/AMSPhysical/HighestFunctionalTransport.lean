import GlobalScalarHighestTransport

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  {q : ℝ} {n : ℕ} {lam : Fin n → ℤ}

theorem CompactHighestRealization.transport_evaluation (hq : q≠0)
    (X : CompactHighestRealization q n V lam) (Y : CompactHighestRealization q n W lam)
    (f : List (Fin n) →₀ ℝ) :
    (X.transport hq Y ⟨loweringEvaluation q n X.action X.highest f,loweringEvaluation_cyclic_mem _ _ _ _ _⟩).val =
      loweringEvaluation q n Y.action Y.highest f :=
  highestCyclicTransport_evaluation q hq n X.action Y.action X.pairing Y.pairing X.compact Y.compact
    X.symmetric Y.symmetric X.definite Y.definite X.highest Y.highest lam
    X.highestE Y.highestE X.highestK Y.highestK (X.highestNorm.trans Y.highestNorm.symm) f

/-- Equality of boundary functionals on lowering words gives equality on
the entire actual irreducible carrier, including all weight multiplicities. -/
theorem CompactHighestRealization.transport_functional_of_lowering (hq : q≠0)
    (X : CompactHighestRealization q n V lam) (Y : CompactHighestRealization q n W lam)
    (f : V →ₗ[ℝ] ℝ) (g : W →ₗ[ℝ] ℝ) (a : ℝ)
    (h : ∀ w,g (typeALoweredVector q n Y.action Y.highest w)=
      a*f (typeALoweredVector q n X.action X.highest w)) (x : X.channel) :
    g (X.transport hq Y x).val = a*f x.val := by
  have hx : x.val∈LinearMap.range (loweringEvaluation q n X.action X.highest) := by
    rw [loweringEvaluation,Finsupp.range_linearCombination]
    change x.val∈typeALoweringSpan q n X.action X.highest
    rw [typeALoweringSpan_eq_cyclic q hq n X.action X.highest lam X.highestE X.highestK]
    exact x.property
  obtain ⟨c,hc⟩:=hx
  have he : x=⟨loweringEvaluation q n X.action X.highest c,loweringEvaluation_cyclic_mem _ _ _ _ _⟩ :=
    Subtype.ext hc.symm
  rw [he,X.transport_evaluation]
  change g (loweringEvaluation q n Y.action Y.highest c)=a*f (loweringEvaluation q n X.action X.highest c)
  clear hc he x
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero,mul_zero]
  | add c d hc hd => simp only [map_add,hc,hd,mul_add]
  | single w b =>
    rw [loweringEvaluation_single,loweringEvaluation_single,map_smul,map_smul,smul_eq_mul,smul_eq_mul,h]
    ring

end AMSPhysical
#print axioms AMSPhysical.CompactHighestRealization.transport_functional_of_lowering
