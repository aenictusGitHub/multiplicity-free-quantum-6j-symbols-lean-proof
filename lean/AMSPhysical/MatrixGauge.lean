import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.Star.Unitary
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace AMSPhysical
open Matrix

variable {n K : Type*} [Fintype n] [DecidableEq n] [Field K]

/-- A matrix commuting with a simple diagonal spectrum must itself be diagonal. -/
theorem simple_diagonal_commutant (theta : n → K) (htheta : Function.Injective theta)
    (M : Matrix n n K) (hM : diagonal theta*M=M*diagonal theta) : M.IsDiag := by
  intro i j hij
  have he := congrArg (fun B : Matrix n n K => B i j) hM
  simp only [diagonal_mul,mul_diagonal] at he
  have hdiff : theta i-theta j≠0 := sub_ne_zero.mpr (fun h => hij (htheta h))
  have hz : (theta i-theta j)*M i j=0 := by linear_combination he
  exact (mul_eq_zero.mp hz).resolve_left hdiff

section Star
variable [StarRing K]

theorem diagonal_unitary_phases (M : unitary (Matrix n n K))
    (hdiag : (M:Matrix n n K).IsDiag) (i : n) :
    star ((M:Matrix n n K) i i)*(M:Matrix n n K) i i=1 := by
  have hd := hdiag.diagonal_diag
  have hm := unitary.coe_star_mul_self M
  rw [← hd] at hm
  have he := congrArg (fun B : Matrix n n K => B i i) hm
  simpa only [star_eq_conjTranspose,diagonal_conjTranspose,diagonal_mul_diagonal,
    diagonal_apply_eq,one_apply_eq,Pi.mul_apply,Function.comp_apply] using he

/-- The ratio of two matched orthonormal eigenframes is a diagonal phase matrix. -/
theorem matched_frame_ratio_diagonal (a b : Matrix n n K) (theta : n → K)
    (htheta : Function.Injective theta) (L L' S : unitary (Matrix n n K))
    (hL : a*(L:Matrix n n K)=(L:Matrix n n K)*diagonal theta)
    (hL' : b*(L':Matrix n n K)=(L':Matrix n n K)*diagonal theta)
    (hS : b*(S:Matrix n n K)=(S:Matrix n n K)*a) :
    ((star L'*S*L : unitary (Matrix n n K)):Matrix n n K).IsDiag := by
  apply simple_diagonal_commutant theta htheta
  change diagonal theta*((star (L':Matrix n n K)*(S:Matrix n n K))*(L:Matrix n n K)) =
    ((star (L':Matrix n n K)*(S:Matrix n n K))*(L:Matrix n n K))*diagonal theta
  have hleft : diagonal theta*star (L':Matrix n n K)=star (L':Matrix n n K)*b := by
    calc
      diagonal theta*star (L':Matrix n n K)=
          (star (L':Matrix n n K)*(L':Matrix n n K))*diagonal theta*star (L':Matrix n n K) := by
            rw [unitary.coe_star_mul_self L',one_mul]
      _=star (L':Matrix n n K)*((L':Matrix n n K)*diagonal theta)*star (L':Matrix n n K) := by
        simp only [mul_assoc]
      _=star (L':Matrix n n K)*(b*(L':Matrix n n K))*star (L':Matrix n n K) := by rw [hL']
      _=star (L':Matrix n n K)*b := by
        have hu : (L':Matrix n n K)*star (L':Matrix n n K)=1 :=
          unitary.coe_mul_star_self L'
        calc
          star (L':Matrix n n K)*(b*(L':Matrix n n K))*star (L':Matrix n n K) =
              star (L':Matrix n n K)*(b*((L':Matrix n n K)*star (L':Matrix n n K))) := by
                simp only [mul_assoc]
          _=star (L':Matrix n n K)*b := by rw [hu,mul_one]
  calc
    diagonal theta*((star (L':Matrix n n K)*(S:Matrix n n K))*(L:Matrix n n K)) =
        (diagonal theta*star (L':Matrix n n K))*(S:Matrix n n K)*(L:Matrix n n K) := by simp only [mul_assoc]
    _=(star (L':Matrix n n K)*b)*(S:Matrix n n K)*(L:Matrix n n K) := by rw [hleft]
    _=star (L':Matrix n n K)*(b*(S:Matrix n n K))*(L:Matrix n n K) := by simp only [mul_assoc]
    _=star (L':Matrix n n K)*((S:Matrix n n K)*a)*(L:Matrix n n K) := by rw [hS]
    _=star (L':Matrix n n K)*(S:Matrix n n K)*(a*(L:Matrix n n K)) := by simp only [mul_assoc]
    _=star (L':Matrix n n K)*(S:Matrix n n K)*((L:Matrix n n K)*diagonal theta) := by rw [hL]
    _=((star (L':Matrix n n K)*(S:Matrix n n K))*(L:Matrix n n K))*diagonal theta := by simp only [mul_assoc]

end Star

/-- Transport of connection matrices, assuming an independently established
intertwining equation for the two connection operators. -/
theorem frame_connection_transport {G : Type*} [Group G]
    (L L' R R' S P P' : G) (hP : P'*S=S*P) :
    R'⁻¹*P'*L'=(R'⁻¹*S*R)*(R⁻¹*P*L)*(L'⁻¹*S*L)⁻¹ := by
  have hp : P'=S*P*S⁻¹ := by
    calc
      P'=P'*(S*S⁻¹) := by rw [mul_inv_cancel,mul_one]
      _=(P'*S)*S⁻¹ := (mul_assoc _ _ _).symm
      _=(S*P)*S⁻¹ := by rw [hP]
  rw [hp]
  group

section Entries
variable [StarRing K]

theorem diagonal_phase_entries (Drow Dcol U : Matrix n n K)
    (hrow : Drow.IsDiag) (hcol : Dcol.IsDiag) (i j : n) :
    (Drow*U*star Dcol) i j=Drow i i*U i j*star (Dcol j j) := by
  rw [← hrow.diagonal_diag,← hcol.diagonal_diag]
  simp only [star_eq_conjTranspose,diagonal_conjTranspose,diagonal_mul,mul_diagonal,
    diag_apply,Function.comp_apply,diagonal_apply_eq]
  rfl

end Entries
end AMSPhysical
#print axioms AMSPhysical.simple_diagonal_commutant
#print axioms AMSPhysical.matched_frame_ratio_diagonal
#print axioms AMSPhysical.frame_connection_transport
#print axioms AMSPhysical.diagonal_phase_entries
