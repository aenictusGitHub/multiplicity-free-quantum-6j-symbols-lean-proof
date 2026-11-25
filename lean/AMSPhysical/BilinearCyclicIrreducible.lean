import BilinearCyclic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3600000
noncomputable section
namespace AMSPhysical
variable {A V I : Type*} [Ring A] [Algebra ℝ A] [AddCommGroup V] [Module ℝ V] [Module.Finite ℝ V]

/-- A unique highest line in a positive, adjoint-closed finite representation
generates an irreducible actual submodule. Orthogonal decomposition is proved
from the restricted bilinear form, with no semisimplicity hypothesis. -/
theorem cyclic_highest_irreducible (ρ : A →ₐ[ℝ] Module.End ℝ V)
    (B : LinearMap.BilinForm ℝ V) (hSym : ∀ x y,B x y=B y x)
    (hDef : ∀ x,B x x=0 → x=0)
    (hAdj : ∀ z : A,∃ u : A,PairAdjoint B (ρ z) (ρ u))
    (e k : I → A) (lam : I → ℝ) (v : V)
    (hvE : ∀ i,ρ (e i) v=0) (hvK : ∀ i,ρ (k i) v=lam i • v)
    (hLine : ∀ w,(∀ i,ρ (e i) w=0) → (∀ i,ρ (k i) w=lam i • w) → ∃ a : ℝ,w=a • v)
    (S : Submodule ℝ V) (hSC : S≤algebraCyclicSpan ρ v) (hS : algebraInvariant ρ S) :
    S=⊥ ∨ S=algebraCyclicSpan ρ v := by
  have hR : LinearMap.BilinForm.IsRefl B := by
    intro x y h
    change B y x=0
    rw [← hSym x y]
    exact h
  have hND : (LinearMap.BilinForm.restrict B S).Nondegenerate := by
    intro x hx
    apply Subtype.ext
    have hh : B x.val x.val=0 := hx x
    exact hDef x.val hh
  have hCompl := LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate (B:=B) hR hND
  have hO := algebraInvariant_orthogonal ρ B hSym hAdj S hS
  have hvSup : v∈S⊔LinearMap.BilinForm.orthogonal B S := by rw [hCompl.sup_eq_top];trivial
  obtain ⟨s,hs,o,ho,hso⟩ := Submodule.mem_sup.mp hvSup
  have hzero (x y : V) (hx : x∈S) (hy : y∈LinearMap.BilinForm.orthogonal B S) (hz : x+y=0) : x=0 := by
    have hxo : x∈LinearMap.BilinForm.orthogonal B S := by
      have he : x= -y := eq_neg_of_add_eq_zero_left hz
      rw [he]
      exact (LinearMap.BilinForm.orthogonal B S).neg_mem hy
    have hh : x∈S⊓LinearMap.BilinForm.orthogonal B S := ⟨hx,hxo⟩
    simpa only [hCompl.inf_eq_bot,Submodule.mem_bot] using hh
  have hsE : ∀ i,ρ (e i) s=0 := by
    intro i
    apply hzero _ (ρ (e i) o) (hS (e i) s hs) (hO (e i) o ho)
    rw [← map_add,hso,hvE]
  have hsK : ∀ i,ρ (k i) s=lam i • s := by
    intro i
    apply sub_eq_zero.mp
    apply hzero _ (ρ (k i) o-lam i • o)
      (S.sub_mem (hS (k i) s hs) (S.smul_mem _ hs))
      ((LinearMap.BilinForm.orthogonal B S).sub_mem (hO (k i) o ho) ((LinearMap.BilinForm.orthogonal B S).smul_mem _ ho))
    calc
      _ = ρ (k i) (s+o)-lam i • (s+o) := by rw [map_add,smul_add];abel
      _ = 0 := by rw [hso,hvK,sub_self]
  obtain ⟨c,hsc⟩ := hLine s hsE hsK
  by_cases hc : c=0
  · left
    have hs0 : s=0 := by rw [hsc,hc,zero_smul]
    have hvo : v∈LinearMap.BilinForm.orthogonal B S := by rw [← hso,hs0,zero_add];exact ho
    have hCO := algebraCyclicSpan_minimal ρ v (LinearMap.BilinForm.orthogonal B S) hO hvo
    have hSO : S≤LinearMap.BilinForm.orthogonal B S := le_trans hSC hCO
    have hInf : S⊓LinearMap.BilinForm.orthogonal B S=S := inf_eq_left.mpr hSO
    rw [← hInf,hCompl.inf_eq_bot]
  · right
    have hvs : v∈S := by
      rw [hsc] at hs
      exact (S.smul_mem_iff hc).mp hs
    exact le_antisymm hSC (algebraCyclicSpan_minimal ρ v S hS hvs)

end AMSPhysical
#print axioms AMSPhysical.cyclic_highest_irreducible
