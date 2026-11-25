import CompactHighestRealization
import CompactFormScaling

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4200000
noncomputable section
namespace AMSPhysical
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- Every actual intertwiner from a complete compact highest module scales
the physical metric by its ACTUAL highest-vector squared norm. This does
not assume injectivity or an already normalized target vector. -/
theorem compactHighestIntertwiner_metric (q : ℝ) (hq : q≠0) (n : ℕ) (lam : Fin n → ℤ)
    (X : CompactHighestRealization q n V lam) (hSpan : X.channel=⊤)
    (σ : UqTypeA q n →ₐ[ℝ] Module.End ℝ W) (C : LinearMap.BilinForm ℝ W)
    (hC : IsCompactTypeAPair q n C σ) (hSymC : ∀ v w,C v w=C w v)
    (T : V →ₗ[ℝ] W) (hT : ∀ z v,T (X.action z v)=σ z (T v)) (v w : V) :
    C (T v) (T w)=C (T X.highest) (T X.highest)*X.pairing v w := by
  let c:=C (T X.highest) (T X.highest)
  have hSymScaled : ∀ v w,(c • X.pairing) v w=(c • X.pairing) w v := by
    intro v w
    change c*X.pairing v w=c*X.pairing w v
    rw [X.symmetric]
  have hE : ∀ i,σ (typeAAlgebraGenerator q n i 0) (T X.highest)=0 := by
    intro i
    rw [← hT,X.highestE,map_zero]
  have hK : ∀ i,σ (typeAAlgebraGenerator q n i 2) (T X.highest)=q^(lam i) • T X.highest := by
    intro i
    rw [← hT,X.highestK,map_smul]
  have hNorm : (c • X.pairing) X.highest X.highest=C (T X.highest) (T X.highest) := by
    change c*X.pairing X.highest X.highest=c
    rw [X.highestNorm,mul_one]
  have hGram:=highest_lowering_Gram_unique q hq n X.action σ (c • X.pairing) C
    (compactTypeAPair_scale q n _ _ X.compact c) hC hSymScaled hSymC X.highest (T X.highest) lam
    X.highestE hE X.highestK hK hNorm
  have hLower (u : List (Fin n)) :
      T (typeALoweredVector q n X.action X.highest u)=typeALoweredVector q n σ (T X.highest) u :=
    hT (typeALoweringWord q n u) X.highest
  have hG : ∀ u t,(c • X.pairing) (typeALoweredVector q n X.action X.highest u)
      (typeALoweredVector q n X.action X.highest t)=
    C (T (typeALoweredVector q n X.action X.highest u)) (T (typeALoweredVector q n X.action X.highest t)) := by
    intro u t
    rw [hLower,hLower]
    exact hGram u t
  have hAll : LinearMap.range (Finsupp.linearCombination ℝ (typeALoweredVector q n X.action X.highest))=⊤ := by
    rw [Finsupp.range_linearCombination]
    change typeALoweringSpan q n X.action X.highest=⊤
    rw [typeALoweringSpan_eq_cyclic q hq n X.action X.highest lam X.highestE X.highestK]
    exact hSpan
  obtain ⟨f,hf⟩:=LinearMap.range_eq_top.mp hAll v
  obtain ⟨g,hg⟩:=LinearMap.range_eq_top.mp hAll w
  have he:=linearCombination_pair_congr (c • X.pairing) C
    (typeALoweredVector q n X.action X.highest) (fun u =>T (typeALoweredVector q n X.action X.highest u)) hG f g
  have hMap (a : List (Fin n) →₀ ℝ) :
      Finsupp.linearCombination ℝ (fun u =>T (typeALoweredVector q n X.action X.highest u)) a=
        T (Finsupp.linearCombination ℝ (typeALoweredVector q n X.action X.highest) a) := by
    simp only [Finsupp.linearCombination_apply,Finsupp.sum,map_sum,map_smul]
  rw [hMap,hMap,hf,hg] at he
  exact he.symm

end AMSPhysical
#print axioms AMSPhysical.compactHighestIntertwiner_metric
