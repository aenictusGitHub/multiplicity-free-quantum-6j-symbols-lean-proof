import AlgebraIntertwinerSpace
import CompactHighestExtension
import QuantumTypeAHighestSpace

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

def compactHighestHomEvaluation (q : ℝ) (n : ℕ) (lam : Fin n → ℤ)
    (X : CompactHighestRealization q n V lam) (σ : UqTypeA q n →ₐ[ℝ] Module.End ℝ W) :
    algebraIntertwinerSpace X.action σ →ₗ[ℝ] typeAHighestSpace q n σ lam where
  toFun f := ⟨f.val X.highest,by
    apply (mem_typeAHighestSpace q n σ lam _).mpr
    constructor
    · intro i
      rw [← f.property,X.highestE,map_zero]
    · intro i
      rw [← f.property,X.highestK,map_smul]⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

theorem compactHighestHomEvaluation_injective (q : ℝ) (n : ℕ) (lam : Fin n → ℤ)
    (X : CompactHighestRealization q n V lam) (hSpan : X.channel=⊤)
    (σ : UqTypeA q n →ₐ[ℝ] Module.End ℝ W) :
    Function.Injective (compactHighestHomEvaluation q n lam X σ) := by
  intro f g he
  apply Subtype.ext
  exact algebraIntertwiner_cyclic_unique X.action σ X.highest hSpan f.val g.val f.property g.property
    (congrArg Subtype.val he)

theorem compactHighestHomEvaluation_surjective (q : ℝ) (hq : q≠0) (n : ℕ) (lam : Fin n → ℤ)
    (X : CompactHighestRealization q n V lam) (hSpan : X.channel=⊤)
    (σ : UqTypeA q n →ₐ[ℝ] Module.End ℝ W) (C : W →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (hC : IsCompactTypeAPair q n C σ) (hSymC : ∀ v w,C v w=C w v) (hDefC : ∀ v,C v v=0 → v=0) :
    Function.Surjective (compactHighestHomEvaluation q n lam X σ) := by
  intro w
  have hHighest:=(mem_typeAHighestSpace q n σ lam w.val).mp w.property
  obtain ⟨f,hf,hfw⟩:=compactHighest_intertwiner_exists q hq n lam X hSpan σ C hC hSymC hDefC w.val hHighest.1 hHighest.2
  exact ⟨⟨f,hf⟩,Subtype.ext hfw⟩

/-- Actual Hom/highest-space equivalence; surjectivity is proved by compact
highest transport, not supplied as a dimension or physical-identification axiom. -/
def compactHighestHomEquiv (q : ℝ) (hq : q≠0) (n : ℕ) (lam : Fin n → ℤ)
    (X : CompactHighestRealization q n V lam) (hSpan : X.channel=⊤)
    (σ : UqTypeA q n →ₐ[ℝ] Module.End ℝ W) (C : W →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (hC : IsCompactTypeAPair q n C σ) (hSymC : ∀ v w,C v w=C w v) (hDefC : ∀ v,C v v=0 → v=0) :
    algebraIntertwinerSpace X.action σ ≃ₗ[ℝ] typeAHighestSpace q n σ lam :=
  LinearEquiv.ofBijective (compactHighestHomEvaluation q n lam X σ)
    ⟨compactHighestHomEvaluation_injective q n lam X hSpan σ,
      compactHighestHomEvaluation_surjective q hq n lam X hSpan σ C hC hSymC hDefC⟩

end AMSPhysical
#print axioms AMSPhysical.compactHighestHomEquiv
