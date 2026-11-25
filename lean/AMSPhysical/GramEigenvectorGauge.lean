import OrthonormalChannelLine

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
noncomputable section
namespace AMSPhysical
variable {I V:Type*} [Fintype I] [DecidableEq I] [AddCommGroup V] [Module ℝ V]

/-- A unit eigenvector of a symmetric Gram form is the corresponding
orthonormal basis vector up to ONE channel sign when the eigenvalues are
pairwise distinct. No entry-dependent sign is introduced. -/
theorem gramEigen_unit_unique_sign (B G:LinearMap.BilinForm ℝ V)
    (hB:∀ x y,B x y=B y x) (hG:∀ x y,G x y=G y x)
    (b:Module.Basis I ℝ V) (hb:∀ i j,B (b i) (b j)=if i=j then 1 else 0)
    (ev:I → ℝ) (hi:Function.Injective ev) (hbg:∀ x i,G x (b i)=ev i*B x (b i))
    (i:I) (v:V) (hv:∀ x,G x v=ev i*B x v) (hn:B v v=1):
    ∃ e:ℝ,(e=1 ∨ e= -1) ∧ v=e • b i := by
  apply unit_vector_on_orthonormal_channel_line B b hb i v _ hn
  intro j hji
  have he:ev i*B (b j) v=ev j*B (b j) v:=by
    rw [← hv, hG, hbg, hB v (b j)]
  have hz:(ev i-ev j)*B (b j) v=0:=by linear_combination he
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (fun h=>hji (hi h.symm)))

variable {W V' W':Type*} [AddCommGroup W] [Module ℝ W]
  [AddCommGroup V'] [Module ℝ V'] [AddCommGroup W'] [Module ℝ W']

theorem scaledCreationGram_transport (B':LinearMap.BilinForm ℝ V') (C':LinearMap.BilinForm ℝ W')
    (e:V ≃ₗ[ℝ] W) (f:V' ≃ₗ[ℝ] W') (A:V →ₗ[ℝ] V') (D:W →ₗ[ℝ] W') (γ:ℝ)
    (hf:∀ x y,C' (f x) (f y)=B' x y) (hA:∀ x,f (A x)=γ • D (e x)) (v w:V):
    γ^2*C' (D (e v)) (D (e w))=B' (A v) (A w) := by
  calc
    _=C' (γ • D (e v)) (γ • D (e w)):=by
      simp only [map_smul,LinearMap.smul_apply,smul_eq_mul]
      ring
    _=_:=by rw [← hA,← hA,hf]

end AMSPhysical
#print axioms AMSPhysical.gramEigen_unit_unique_sign
#print axioms AMSPhysical.scaledCreationGram_transport
