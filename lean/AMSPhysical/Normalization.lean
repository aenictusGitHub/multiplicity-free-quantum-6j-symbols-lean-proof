import Mathlib.Tactic
import Mathlib.Algebra.Order.Field.Power

set_option autoImplicit false
noncomputable section

namespace AMSPhysical

variable {K : Type*} [Field K]

def factorialConstant (F : ℕ → K) (h : ℕ) : K := F (h+1)*F h

/-- Square of the rank-(h+2) triangle factor, in nonnegative triangle coordinates. -/
def triangleSq (F : ℕ → K) (h p q u : ℕ) : K :=
  F u*F p*F q/F (p+q+u+h+1)

/-- The mixed-channel quantum Weyl expression; qnum and factorial remain explicit inputs. -/
def mixedWeyl (F g : ℕ → K) (h p q : ℕ) : K :=
  g (p+q+h+1)*F (p+h)*F (q+h)/(F p*F q*factorialConstant F h)

def sameWeyl (F g : ℕ → K) (h p q t : ℕ) : K :=
  g (p+q+1)*F (p+q+t+h+1)*F (t+h)/
    (F (p+q+t+1)*F t*factorialConstant F h)

theorem mixed_normalization_cancel (F g : ℕ → K)
    (hF : ∀ n, F n≠0) (h p q u v : ℕ) :
    mixedWeyl F g h p q * factorialConstant F h *
      triangleSq F h p q u * triangleSq F h q p v /
      (triangleSq F 0 p (q+h) u * triangleSq F 0 q (p+h) v) =
      g (p+q+h+1) := by
  simp only [mixedWeyl, factorialConstant, triangleSq, Nat.add_zero]
  simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  field_simp [hF]

theorem same_normalization_cancel (F g : ℕ → K)
    (hF : ∀ n, F n≠0) (h p q p' q' t : ℕ) (hsum : p'+q'=p+q) :
    sameWeyl F g h p q t * factorialConstant F h *
      triangleSq F h p q t * triangleSq F h p' q' t /
      (triangleSq F 0 p q (t+h) * triangleSq F 0 p' q' t) =
      g (p+q+1) := by
  simp only [sameWeyl, factorialConstant, triangleSq, Nat.add_zero]
  rw [hsum]
  simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  field_simp [hF]

/-- A quantum integer represented by a finite geometric sum, including v=1. -/
def qnum (v : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, v ^ ((n:ℤ)-1-2*k)

def qfactorial (v : ℝ) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, qnum v (k+1)

theorem qnum_pos (v : ℝ) (hv : 0<v) (n : ℕ) (hn : 0<n) : 0<qnum v n := by
  unfold qnum
  apply Finset.sum_pos
  · intro k hk
    exact zpow_pos hv _
  · exact ⟨0,Finset.mem_range.mpr hn⟩

theorem qfactorial_pos (v : ℝ) (hv : 0<v) (n : ℕ) : 0<qfactorial v n := by
  unfold qfactorial
  apply Finset.prod_pos
  intro k hk
  exact qnum_pos v hv (k+1) (by omega)

theorem qfactorial_ne_zero (v : ℝ) (hv : 0<v) (n : ℕ) : qfactorial v n≠0 :=
  ne_of_gt (qfactorial_pos v hv n)

theorem quantum_mixed_normalization (v : ℝ) (hv : 0<v) (h p q u w : ℕ) :
    mixedWeyl (qfactorial v) (qnum v) h p q * factorialConstant (qfactorial v) h *
      triangleSq (qfactorial v) h p q u * triangleSq (qfactorial v) h q p w /
      (triangleSq (qfactorial v) 0 p (q+h) u *
        triangleSq (qfactorial v) 0 q (p+h) w) = qnum v (p+q+h+1) :=
  mixed_normalization_cancel _ _ (qfactorial_ne_zero v hv) _ _ _ _ _

theorem quantum_same_normalization (v : ℝ) (hv : 0<v)
    (h p q p' q' t : ℕ) (hsum : p'+q'=p+q) :
    sameWeyl (qfactorial v) (qnum v) h p q t * factorialConstant (qfactorial v) h *
      triangleSq (qfactorial v) h p q t * triangleSq (qfactorial v) h p' q' t /
      (triangleSq (qfactorial v) 0 p q (t+h) *
        triangleSq (qfactorial v) 0 p' q' t) = qnum v (p+q+1) :=
  same_normalization_cancel _ _ (qfactorial_ne_zero v hv) _ _ _ _ _ _ hsum

theorem qnum_one (n : ℕ) : qnum 1 n = (n : ℝ) := by simp [qnum]

theorem qnum_succ (v : ℝ) (hv : v≠0) (n : ℕ) :
    qnum v (n+1) = v*qnum v n + v^(-(n:ℤ)) := by
  unfold qnum
  rw [Finset.sum_range_succ]
  have hlast : ((n+1:ℕ):ℤ)-1-2*(n:ℤ) = -(n:ℤ) := by omega
  rw [hlast]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have he : ((n+1:ℕ):ℤ)-1-2*(k:ℤ) = 1+((n:ℤ)-1-2*(k:ℤ)) := by omega
  rw [he,zpow_add₀ hv,zpow_one]

theorem qnum_mul_denominator (v : ℝ) (hv : v≠0) (n : ℕ) :
    (v-v⁻¹)*qnum v n = v^(n:ℤ)-v^(-(n:ℤ)) := by
  induction n with
  | zero => simp [qnum]
  | succ n ih =>
    rw [qnum_succ v hv]
    have hp : v^((n+1:ℕ):ℤ) = v^(n:ℤ)*v := by
      simp [Nat.cast_add,zpow_add₀ hv]
    have hn : v^(-((n+1:ℕ):ℤ)) = v^(-(n:ℤ))*v⁻¹ := by
      rw [Nat.cast_add,Nat.cast_one,neg_add,zpow_add₀ hv]
      simp
    rw [hp,hn]
    calc
      (v-v⁻¹)*(v*qnum v n+v^(-(n:ℤ))) =
          v*((v-v⁻¹)*qnum v n)+v*v^(-(n:ℤ))-v⁻¹*v^(-(n:ℤ)) := by ring
      _ = v*(v^(n:ℤ)-v^(-(n:ℤ)))+v*v^(-(n:ℤ))-v⁻¹*v^(-(n:ℤ)) := by rw [ih]
      _ = v^(n:ℤ)*v-v^(-(n:ℤ))*v⁻¹ := by ring

theorem qnum_eq_standard (v : ℝ) (hv : v≠0) (hden : v-v⁻¹≠0) (n : ℕ) :
    qnum v n = (v^n-v^(-(n:ℤ)))/(v-v⁻¹) := by
  apply (eq_div_iff hden).mpr
  simpa [mul_comm,zpow_natCast] using qnum_mul_denominator v hv n

end AMSPhysical

#print axioms AMSPhysical.mixed_normalization_cancel
#print axioms AMSPhysical.same_normalization_cancel
#print axioms AMSPhysical.quantum_mixed_normalization
