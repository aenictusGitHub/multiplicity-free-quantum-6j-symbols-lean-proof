import BilinearCyclic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
variable {A V W : Type*} [Ring A] [Algebra ℝ A] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]

def algebraIntertwinerSpace (ρ : A →ₐ[ℝ] Module.End ℝ V) (σ : A →ₐ[ℝ] Module.End ℝ W) :
    Submodule ℝ (V →ₗ[ℝ] W) where
  carrier := {f | ∀ z v,f (ρ z v)=σ z (f v)}
  zero_mem' := by intro z v;simp
  add_mem' := by
    intro f g hf hg z v
    change f (ρ z v)+g (ρ z v)=σ z (f v+g v)
    rw [hf,hg,map_add]
  smul_mem' := by
    intro c f hf z v
    change c • f (ρ z v)=σ z (c • f v)
    rw [hf,map_smul]

theorem algebraIntertwiner_cyclic_unique (ρ : A →ₐ[ℝ] Module.End ℝ V) (σ : A →ₐ[ℝ] Module.End ℝ W)
    (v : V) (hSpan : algebraCyclicSpan ρ v=⊤) (f g : V →ₗ[ℝ] W)
    (hf : ∀ z w,f (ρ z w)=σ z (f w)) (hg : ∀ z w,g (ρ z w)=σ z (g w)) (hfg : f v=g v) : f=g := by
  have hInv : algebraInvariant ρ (LinearMap.eqLocus f g) := by
    intro z w hw
    change f (ρ z w)=g (ρ z w)
    rw [hf,hg]
    exact congrArg (σ z) hw
  have hIncl:=algebraCyclicSpan_minimal ρ v (LinearMap.eqLocus f g) hInv hfg
  apply LinearMap.ext
  intro w
  apply hIncl
  rw [hSpan]
  trivial

def algebraIntertwinerEvaluation (ρ : A →ₐ[ℝ] Module.End ℝ V) (σ : A →ₐ[ℝ] Module.End ℝ W) (v : V) :
    algebraIntertwinerSpace ρ σ →ₗ[ℝ] W where
  toFun f := f.val v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem algebraIntertwinerEvaluation_injective (ρ : A →ₐ[ℝ] Module.End ℝ V) (σ : A →ₐ[ℝ] Module.End ℝ W)
    (v : V) (hSpan : algebraCyclicSpan ρ v=⊤) : Function.Injective (algebraIntertwinerEvaluation ρ σ v) := by
  intro f g he
  apply Subtype.ext
  exact algebraIntertwiner_cyclic_unique ρ σ v hSpan f.val g.val f.property g.property he

end AMSPhysical
