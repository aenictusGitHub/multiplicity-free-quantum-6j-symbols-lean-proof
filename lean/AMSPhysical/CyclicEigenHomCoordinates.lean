import AlgebraIntertwinerSpace
import KroneckerEigenExpansion

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
variable {A V W I J H : Type*} [Ring A] [Algebra ℝ A]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [DecidableEq H]

def MatchingWeightPair (lam : I → H) (mu : J → H) := {p : I×J // lam p.1=mu p.2}

instance matchingWeightPairFintype (lam : I → H) (mu : J → H) : Fintype (MatchingWeightPair lam mu) :=
  inferInstanceAs (Fintype {p : I×J // lam p.1=mu p.2})

def cyclicEigenHomCoordinates (ρ : A →ₐ[ℝ] Module.End ℝ V) (σ : A →ₐ[ℝ] Module.End ℝ W)
    (v : I → V) (C : J → Module.Dual ℝ W) (lam : I → H) (mu : J → H) :
    algebraIntertwinerSpace ρ σ →ₗ[ℝ] (MatchingWeightPair lam mu → ℝ) where
  toFun f p := C p.val.2 (f.val (v p.val.1))
  map_add' _ _ := by ext p;exact map_add _ _ _
  map_smul' _ _ := by ext p;exact map_smul _ _ _

theorem intertwiner_zero_of_cyclic_family
    (ρ : A →ₐ[ℝ] Module.End ℝ V) (σ : A →ₐ[ℝ] Module.End ℝ W)
    (v : I → V) (hSpan : (⨆ i,algebraCyclicSpan ρ (v i))=⊤)
    (f : V →ₗ[ℝ] W) (hf : ∀ z w,f (ρ z w)=σ z (f w)) (hv : ∀ i,f (v i)=0) : f=0 := by
  have hIncl : (⨆ i,algebraCyclicSpan ρ (v i))≤LinearMap.ker f := by
    apply iSup_le
    intro i
    apply algebraCyclicSpan_minimal ρ (v i) (LinearMap.ker f)
    · intro z w hw
      change f (ρ z w)=0
      rw [hf,show f w=0 from hw,map_zero]
    · exact hv i
  apply LinearMap.ext
  intro w
  apply hIncl
  rw [hSpan]
  trivial

/-- Actual intertwiners are detected by the matching eigenweight entries of
their images on a complete family of independently constructed cyclic vectors. -/
theorem cyclicEigenHomCoordinates_injective
    (ρ : A →ₐ[ℝ] Module.End ℝ V) (σ : A →ₐ[ℝ] Module.End ℝ W)
    (v : I → V) (b : J → W) (C : J → Module.Dual ℝ W)
    (lam : I → H) (mu : J → H) (a : H → ℝ) (ha : Function.Injective a) (z : A)
    (hSpan : (⨆ i,algebraCyclicSpan ρ (v i))=⊤)
    (hb : LinearIndependent ℝ b)
    (hv : ∀ i,ρ z (v i)=a (lam i) • v i)
    (hB : ∀ j,σ z (b j)=a (mu j) • b j)
    (hExp : ∀ f : algebraIntertwinerSpace ρ σ,∀ i,f.val (v i)=∑ j,C j (f.val (v i)) • b j) :
    Function.Injective (cyclicEigenHomCoordinates ρ σ v C lam mu) := by
  intro f g hfg
  have hz : cyclicEigenHomCoordinates ρ σ v C lam mu (f-g)=0 := by
    rw [map_sub,hfg,sub_self]
  have hfzero : (f-g).val=0 := by
    apply intertwiner_zero_of_cyclic_family ρ σ v hSpan (f-g).val (f-g).property
    intro i
    have hE : σ z ((f-g).val (v i))=a (lam i) • (f-g).val (v i) := by
      rw [← (f-g).property,hv,map_smul]
    have hCoords : ∀ j,C j ((f-g).val (v i))=0 := by
      intro j
      by_cases he : lam i=mu j
      · exact congrFun hz ⟨(i,j),he⟩
      · have heq : (∑ j,(C j ((f-g).val (v i))*a (mu j)) • b j)=
            ∑ j,(a (lam i)*C j ((f-g).val (v i))) • b j := by
          calc
            _ = σ z (∑ j,C j ((f-g).val (v i)) • b j) := by simp only [map_sum,map_smul,hB,smul_smul]
            _ = σ z ((f-g).val (v i)) := congrArg (σ z) (hExp (f-g) i).symm
            _ = a (lam i) • (f-g).val (v i) := hE
            _ = _ := by
              conv_lhs => rw [hExp (f-g) i]
              simp only [Finset.smul_sum,smul_smul]
        have h:=hb.eq_coords_of_eq heq j
        have hp : C j ((f-g).val (v i))*(a (mu j)-a (lam i))=0 := by linear_combination h
        apply (mul_eq_zero.mp hp).resolve_right
        exact sub_ne_zero.mpr (fun hh =>he (ha hh).symm)
    rw [hExp (f-g) i]
    simp only [hCoords,zero_smul,Finset.sum_const_zero]
  apply sub_eq_zero.mp
  exact Subtype.ext hfzero

end AMSPhysical
#print axioms AMSPhysical.cyclicEigenHomCoordinates_injective
