import OrthonormalBasisChange

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
variable {I V : Type*} [Fintype I] [DecidableEq I] [AddCommGroup V] [Module ℝ V]

theorem unit_vector_on_orthonormal_channel_line (B : LinearMap.BilinForm ℝ V) (b : Module.Basis I ℝ V)
    (hb : ∀ i j,B (b i) (b j)=if i=j then 1 else 0) (i : I) (v : V)
    (hv : ∀ j,j≠i → B (b j) v=0) (hn : B v v=1) :
    ∃ e : ℝ,(e=1 ∨ e= -1) ∧ v=e • b i := by
  have hcoeff : ∀ j,j≠i → b.repr v j=0 := by
    intro j hji
    rw [← orthonormal_basis_coord_right B b hb j v]
    exact hv j hji
  have he : v=(b.repr v i) • b i := by
    calc
      _ = ∑ j,b.repr v j • b j := (b.sum_repr v).symm
      _ = _ := by
        apply Finset.sum_eq_single i
        · intro j _ hji
          rw [hcoeff j hji,zero_smul]
        · simp
  refine ⟨b.repr v i,?_,he⟩
  rw [he] at hn
  simp only [map_smul,LinearMap.smul_apply,smul_eq_mul,hb,if_pos rfl,ite_true,mul_one] at hn
  have hprod : (b.repr v i-1)*(b.repr v i+1)=0 := by nlinarith
  rcases mul_eq_zero.mp hprod with h|h
  · left;linarith
  · right;linarith

end AMSPhysical
#print axioms AMSPhysical.unit_vector_on_orthonormal_channel_line
