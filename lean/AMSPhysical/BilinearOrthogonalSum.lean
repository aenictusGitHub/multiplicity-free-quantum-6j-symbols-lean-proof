import BilinearCyclic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
variable {V I : Type*} [AddCommGroup V] [Module ℝ V] [Fintype I] [DecidableEq I]

def submoduleFamilySum (S : I → Submodule ℝ V) : (∀ i,S i) →ₗ[ℝ] V where
  toFun x := ∑ i,(x i).val
  map_add' x y := by simp only [Pi.add_apply,Submodule.coe_add,Finset.sum_add_distrib]
  map_smul' a x := by
    simp only [Pi.smul_apply,Submodule.coe_smul,Finset.smul_sum,RingHom.id_apply]

theorem submoduleFamilySum_single (S : I → Submodule ℝ V) (i : I) (x : S i) :
    submoduleFamilySum S (Pi.single i x)=x.val := by
  classical
  change (∑ j,((Pi.single i x : ∀ j,S j) j).val)=x.val
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    simp [Pi.single_apply,hji,Ne.symm hji]
  · simp

theorem submoduleFamilySum_surjective (S : I → Submodule ℝ V) (hS : (⨆ i,S i)=⊤) :
    Function.Surjective (submoduleFamilySum S) := by
  classical
  have hle : (⨆ i,S i)≤LinearMap.range (submoduleFamilySum S) := by
    apply iSup_le
    intro i v hv
    exact ⟨Pi.single i ⟨v,hv⟩,submoduleFamilySum_single S i ⟨v,hv⟩⟩
  intro v
  apply hle
  rw [hS]
  trivial

theorem submoduleFamilySum_pair (B : LinearMap.BilinForm ℝ V) (S : I → Submodule ℝ V)
    (hOrth : ∀ i j,i≠j → ∀ x∈S i,∀ y∈S j,B x y=0)
    (x : ∀ i,S i) (i : I) (y : S i) :
    B (submoduleFamilySum S x) y.val=B (x i).val y.val := by
  classical
  change B (∑ j,(x j).val) y.val=_
  rw [map_sum,LinearMap.sum_apply]
  apply Finset.sum_eq_single i
  · intro j hj hji
    exact hOrth j i hji _ (x j).property _ y.property
  · simp

theorem submoduleFamilySum_injective (B : LinearMap.BilinForm ℝ V)
    (hDef : ∀ x,B x x=0 → x=0) (S : I → Submodule ℝ V)
    (hOrth : ∀ i j,i≠j → ∀ x∈S i,∀ y∈S j,B x y=0) :
    Function.Injective (submoduleFamilySum S) := by
  have hKer : ∀ x : ∀ i,S i,submoduleFamilySum S x=0 → x=0 := by
    intro x hx
    funext i
    apply Subtype.ext
    change (x i).val=0
    apply hDef
    have h := submoduleFamilySum_pair B S hOrth x i (x i)
    rw [hx,map_zero,LinearMap.zero_apply] at h
    exact h.symm
  intro x y he
  apply sub_eq_zero.mp
  apply hKer
  rw [map_sub,he,sub_self]

theorem submoduleFamilySum_isometry (B : LinearMap.BilinForm ℝ V) (S : I → Submodule ℝ V)
    (hOrth : ∀ i j,i≠j → ∀ x∈S i,∀ y∈S j,B x y=0)
    (x y : ∀ i,S i) :
    B (submoduleFamilySum S x) (submoduleFamilySum S y)=∑ i,B (x i).val (y i).val := by
  change B (submoduleFamilySum S x) (∑ i,(y i).val)=_
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact submoduleFamilySum_pair B S hOrth x i (y i)

/-- The actual orthogonal direct-sum identification, constructed from the
proved spanning and pairwise orthogonality of its actual submodules. -/
def orthogonalFamilyEquiv (B : LinearMap.BilinForm ℝ V)
    (hDef : ∀ x,B x x=0 → x=0) (S : I → Submodule ℝ V)
    (hOrth : ∀ i j,i≠j → ∀ x∈S i,∀ y∈S j,B x y=0) (hSpan : (⨆ i,S i)=⊤) :
    (∀ i,S i) ≃ₗ[ℝ] V :=
  LinearEquiv.ofBijective (submoduleFamilySum S)
    ⟨submoduleFamilySum_injective B hDef S hOrth,submoduleFamilySum_surjective S hSpan⟩

end AMSPhysical
