import FullHighestEmbeddingCoherence
import LinearEigenspaceTransport
import QuantumTypeAHighestSpace

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

theorem positive_unit_vectors_on_line_unique (S : Submodule ℝ W)
    (hS : Module.finrank ℝ S=1) (B : LinearMap.BilinForm ℝ W) (f : W →ₗ[ℝ] ℝ)
    (v w : W) (hv : v∈S) (hw : w∈S) (hvn : B v v=1) (hwn : B w w=1)
    (hvf : 0<f v) (hwf : 0<f w) : v=w := by
  let x : S:=⟨w,hw⟩
  let y : S:=⟨v,hv⟩
  have hx : x≠0 := by
    intro he
    have hz : w=0:=congrArg Subtype.val he
    simp only [hz,map_zero,LinearMap.zero_apply] at hwn
    norm_num at hwn
  obtain ⟨a,ha⟩:=exists_smul_eq_of_finrank_eq_one hS hx y
  have he : v=a • w:=(congrArg Subtype.val ha).symm
  have hn : a^2=1 := by
    rw [he] at hvn
    simpa only [map_smul,LinearMap.smul_apply,smul_eq_mul,hwn,mul_one,pow_two] using hvn
  have hp : (a-1)*(a+1)=0 := by nlinarith
  rcases mul_eq_zero.mp hp with hp|hp
  · have ha1 : a=1:=by linarith
    simpa only [ha1,one_smul] using he
  · have ha1 : a= -1:=by linarith
    rw [he,map_smul,smul_eq_mul,ha1] at hvf
    nlinarith

/-- A common positive boundary determines the actual full unit intertwiner,
whenever the relevant highest line is one-dimensional. -/
theorem CompactHighestRealization.positive_full_intertwiner_unique
    {q : ℝ} {n : ℕ} {lam : Fin n → ℤ}
    (X : CompactHighestRealization q n V lam) (hX : X.channel=⊤)
    (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ W)
    (hLine : Module.finrank ℝ (typeAHighestSpace q n ρ lam)=1)
    (B : LinearMap.BilinForm ℝ W) (f : W →ₗ[ℝ] ℝ) (F G : V →ₗ[ℝ] W)
    (hF : ∀ z v,F (X.action z v)=ρ z (F v))
    (hG : ∀ z v,G (X.action z v)=ρ z (G v))
    (hFn : B (F X.highest) (F X.highest)=1) (hGn : B (G X.highest) (G X.highest)=1)
    (hFp : 0<f (F X.highest)) (hGp : 0<f (G X.highest)) : F=G := by
  apply X.full_intertwiner_unique hX ρ F G hF hG
  apply positive_unit_vectors_on_line_unique (typeAHighestSpace q n ρ lam) hLine B f
    (F X.highest) (G X.highest) _ _ hFn hGn hFp hGp
  · apply (mem_typeAHighestSpace q n ρ lam _).mpr
    constructor
    · intro i;rw [← hF,X.highestE,map_zero]
    · intro i;rw [← hF,X.highestK,map_smul]
  · apply (mem_typeAHighestSpace q n ρ lam _).mpr
    constructor
    · intro i;rw [← hG,X.highestE,map_zero]
    · intro i;rw [← hG,X.highestK,map_smul]

end AMSPhysical
#print axioms AMSPhysical.CompactHighestRealization.positive_full_intertwiner_unique
