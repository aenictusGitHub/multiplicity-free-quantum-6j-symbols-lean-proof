import PreservingEndAlgebra
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

variable {K V ι κ : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]

/-- Jointly separating diagonal operators isolate every basis coordinate in
any invariant submodule. The finite spectral projection is constructed here;
no semisimplicity or diagonal-projection hypothesis is assumed. -/
theorem joint_diagonal_coordinate_mem (b : Module.Basis ι K V) (T : κ → Module.End K V)
    (lam : κ → ι → K) (hEig : ∀ j x,T j (b x)=lam j x • b x)
    (hSep : ∀ x y,x≠y → ∃ j,lam j x≠lam j y)
    (S : Submodule K V) (hS : ∀ j,T j∈preservingEndAlgebra S)
    (v : V) (hv : v∈S) (x : ι) : (b.repr v x) • b x∈S := by
  classical
  have aux : ∀ s : Finset ι,x∉s → ∃ P : Module.End K V,
      P∈preservingEndAlgebra S ∧ P (b x)=b x ∧ ∀ y∈s,P (b y)=0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro hx
      refine ⟨1,(preservingEndAlgebra S).one_mem,rfl,?_⟩
      simp
    | @insert y s hys ih =>
      intro hx
      have hxs : x∉s := by simp only [Finset.mem_insert,not_or] at hx;exact hx.2
      have hxy : x≠y := by intro he;apply hx;exact Finset.mem_insert.mpr (Or.inl he)
      obtain ⟨j,hj⟩ := hSep x y hxy
      obtain ⟨P,hP,hPx,hPz⟩ := ih hxs
      let D : Module.End K V := (lam j x-lam j y)⁻¹ • (T j-lam j y • (1:Module.End K V))
      have hD (z : ι) : D (b z)=((lam j x-lam j y)⁻¹*(lam j z-lam j y)) • b z := by
        simp only [D,LinearMap.smul_apply,LinearMap.sub_apply,Module.End.one_apply,hEig,← sub_smul,smul_smul]
      have hDx : D (b x)=b x := by rw [hD,inv_mul_cancel₀ (sub_ne_zero.mpr hj),one_smul]
      have hDy : D (b y)=0 := by rw [hD,sub_self,mul_zero,zero_smul]
      have hDS : D∈preservingEndAlgebra S :=
        (preservingEndAlgebra S).smul_mem
          ((preservingEndAlgebra S).sub_mem (hS j)
            ((preservingEndAlgebra S).smul_mem (preservingEndAlgebra S).one_mem _)) _
      refine ⟨P*D,(preservingEndAlgebra S).mul_mem hP hDS,?_,?_⟩
      · change P (D (b x))=b x
        rw [hDx,hPx]
      · intro z hz
        change P (D (b z))=0
        rcases Finset.mem_insert.mp hz with he | hz
        · subst z
          rw [hDy,map_zero]
        · rw [hD,map_smul,hPz z hz,smul_zero]
  obtain ⟨P,hPS,hPx,hPz⟩ := aux (Finset.univ.erase x) (by simp)
  have hPv : P v=(b.repr v x) • b x := by
    have he : P v=∑ z,(b.repr v z) • P (b z) := by
      conv_lhs => rw [← b.sum_repr v]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro z hz
      rw [map_smul]
    rw [he,Finset.sum_eq_single x]
    · rw [hPx]
    · intro z hz hzx
      rw [hPz z (by simp [hzx]),smul_zero]
    · simp
  rw [← hPv]
  exact hPS v hv

theorem joint_diagonal_basis_mem (b : Module.Basis ι K V) (T : κ → Module.End K V)
    (lam : κ → ι → K) (hEig : ∀ j x,T j (b x)=lam j x • b x)
    (hSep : ∀ x y,x≠y → ∃ j,lam j x≠lam j y)
    (S : Submodule K V) (hS : ∀ j,T j∈preservingEndAlgebra S)
    (v : V) (hv : v∈S) (hv0 : v≠0) : ∃ x,b x∈S := by
  classical
  have hex : ∃ x,b.repr v x≠0 := by
    by_contra hn
    push_neg at hn
    have hz : b.repr v=0 := by ext x;exact hn x
    apply hv0
    apply b.repr.injective
    simpa only [map_zero] using hz
  obtain ⟨x,hx⟩ := hex
  refine ⟨x,?_⟩
  have hc := joint_diagonal_coordinate_mem b T lam hEig hSep S hS v hv x
  have hh := S.smul_mem (b.repr v x)⁻¹ hc
  simpa only [smul_smul,inv_mul_cancel₀ hx,one_smul] using hh

end AMSPhysical

#print axioms AMSPhysical.joint_diagonal_coordinate_mem
