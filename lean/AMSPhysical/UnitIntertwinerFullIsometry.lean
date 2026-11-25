import HighestSpaceMap
import CompactHighestFullEmbedding

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
variable {V W Z : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  [AddCommGroup Z] [Module ℝ Z] {q : ℝ} {n : ℕ} {lam : Fin n → ℤ}

/-- Unit normalization at the cyclic highest generator implies isometry
on every vector. An actual compact ambient embedding supplies the metric
and compactness, so no one-dimensional weight-space assumption is used. -/
theorem unit_intertwiner_full_isometry (hq : q≠0)
    (X : CompactHighestRealization q n V lam) (hX : X.channel=⊤)
    (σ : UqTypeA q n →ₐ[ℝ] Module.End ℝ W) (τ : UqTypeA q n →ₐ[ℝ] Module.End ℝ Z)
    (B : LinearMap.BilinForm ℝ W) (C : LinearMap.BilinForm ℝ Z)
    (hCompact : IsCompactTypeAPair q n C τ) (hSym : ∀ v w,C v w=C w v)
    (hDef : ∀ v,C v v=0 → v=0)
    (E : W →ₗ[ℝ] Z) (F : V →ₗ[ℝ] W)
    (hE : ∀ z v,E (σ z v)=τ z (E v)) (hF : ∀ z v,F (X.action z v)=σ z (F v))
    (hIso : ∀ v w,C (E v) (E w)=B v w) (hN : B (F X.highest) (F X.highest)=1)
    (v w : V) : B (F v) (F w)=X.pairing v w := by
  let G:=E.comp F
  have hG : ∀ z x,G (X.action z x)=τ z (G x) := by
    intro z x
    change E (F (X.action z x))=τ z (E (F x))
    rw [hF,hE]
  let Y : CompactHighestRealization q n Z lam :=
    { action:=τ
      pairing:=C
      highest:=G X.highest
      compact:=hCompact
      symmetric:=hSym
      definite:=hDef
      highestE:=by intro i;rw [← hG,X.highestE,map_zero]
      highestK:=by intro i;rw [← hG,X.highestK,map_smul]
      highestNorm:=(hIso (F X.highest) (F X.highest)).trans hN }
  have hEqual : G=X.fullEmbedding hq hX Y :=
    X.full_intertwiner_unique hX τ G (X.fullEmbedding hq hX Y) hG
      (X.fullEmbedding_intertwines hq hX Y) (X.fullEmbedding_highest hq hX Y).symm
  have hMetric : C (G v) (G w)=X.pairing v w := by
    rw [hEqual]
    exact X.fullEmbedding_isometry hq hX Y v w
  exact (hIso (F v) (F w)).symm.trans hMetric

end AMSPhysical
#print axioms AMSPhysical.unit_intertwiner_full_isometry
