import CompactHighestRealization
import CompactFormScaling

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- Every actual highest vector with the same weight extends uniquely from
a compact cyclic source. Existence follows from the proved universal Gram
transport, with a derived source-form scale; no identification is assumed. -/
theorem compactHighest_intertwiner_exists (q : ℝ) (hq : q≠0) (n : ℕ) (lam : Fin n → ℤ)
    (X : CompactHighestRealization q n V lam) (hSpan : X.channel=⊤)
    (σ : UqTypeA q n →ₐ[ℝ] Module.End ℝ W) (C : W →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (hC : IsCompactTypeAPair q n C σ) (hSymC : ∀ v w,C v w=C w v)
    (hDefC : ∀ v,C v v=0 → v=0) (w : W)
    (hE : ∀ i,σ (typeAAlgebraGenerator q n i 0) w=0)
    (hK : ∀ i,σ (typeAAlgebraGenerator q n i 2) w=q^(lam i) • w) :
    ∃ f : V →ₗ[ℝ] W,(∀ z v,f (X.action z v)=σ z (f v)) ∧ f X.highest=w := by
  by_cases hw : w=0
  · subst w
    exact ⟨0,by simp,by simp⟩
  · let c := C w w
    have hc : c≠0 := by intro he;exact hw (hDefC w he)
    have hScaled : IsCompactTypeAPair q n (c • X.pairing) X.action := compactTypeAPair_scale q n _ _ X.compact c
    have hSymScaled : ∀ v u,(c • X.pairing) v u=(c • X.pairing) u v := by
      intro v u
      change c*X.pairing v u=c*X.pairing u v
      rw [X.symmetric]
    have hDefScaled : ∀ v,(c • X.pairing) v v=0 → v=0 := by
      intro v he
      change c*X.pairing v v=0 at he
      exact X.definite v ((mul_eq_zero.mp he).resolve_left hc)
    have hNorm : (c • X.pairing) X.highest X.highest=C w w := by
      change c*X.pairing X.highest X.highest=C w w
      rw [X.highestNorm,mul_one]
    let T := highestCyclicTransport q hq n X.action σ (c • X.pairing) C hScaled hC
      hSymScaled hSymC hDefScaled hDefC X.highest w lam X.highestE hE X.highestK hK hNorm
    have hAll (v : V) : v∈X.channel := by rw [hSpan];trivial
    let s : V →ₗ[ℝ] X.channel := LinearMap.codRestrict X.channel LinearMap.id hAll
    let f : V →ₗ[ℝ] W := (algebraCyclicSpan σ w).subtype.comp (T.toLinearMap.comp s)
    refine ⟨f,?_,?_⟩
    · intro z v
      change (T ⟨X.action z v,hAll _⟩).val=σ z (T ⟨v,hAll v⟩).val
      exact highestCyclicTransport_intertwines q hq n X.action σ (c • X.pairing) C hScaled hC
        hSymScaled hSymC hDefScaled hDefC X.highest w lam X.highestE hE X.highestK hK hNorm z ⟨v,hAll v⟩
    · change (T ⟨X.highest,hAll _⟩).val=w
      exact highestCyclicTransport_highest q hq n X.action σ (c • X.pairing) C hScaled hC
        hSymScaled hSymC hDefScaled hDefC X.highest w lam X.highestE hE X.highestK hK hNorm

end AMSPhysical
#print axioms AMSPhysical.compactHighest_intertwiner_exists
