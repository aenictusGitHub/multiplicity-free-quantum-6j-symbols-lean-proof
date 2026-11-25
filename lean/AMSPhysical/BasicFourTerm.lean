import QRacahFiniteSeries
import BasicHypergeometricTerm

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

def basic4Term (Q A B C U E F G : ℝ) (k : ℕ) : ℝ :=
  qPochhammer Q A k*qPochhammer Q B k*qPochhammer Q C k*qPochhammer Q U k*Q^k/
    (qPochhammer Q Q k*qPochhammer Q E k*qPochhammer Q F k*qPochhammer Q G k)

theorem qRacahTerm_basic4 (Q A B C D N t : ℝ) (k : ℕ) :
    qRacahCoefficient Q A B C D N k*qRacahNewton Q (C*D) t k=
      basic4Term Q (A*B*Q*N) t⁻¹ (C*D*Q*t) N⁻¹ (A*Q) (B*D*Q) (C*Q) k := by
  unfold qRacahCoefficient qRacahNewton basic4Term
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem basic4Term_cancel_middle (Q A B U E F G : ℝ) (k : ℕ)
    (hF : qPochhammer Q F k≠0) :
    basic4Term Q A B F U E F G k=basic3Term Q A B U E G k := by
  unfold basic4Term basic3Term
  simp only [div_eq_mul_inv,mul_inv_rev]
  have h := inv_mul_cancel₀ hF
  linear_combination qPochhammer Q A k*qPochhammer Q B k*qPochhammer Q U k*Q^k*
    (qPochhammer Q Q k)⁻¹*(qPochhammer Q E k)⁻¹*(qPochhammer Q G k)⁻¹*h

theorem basic4Term_cancel_first (Q A B U E F G : ℝ) (k : ℕ)
    (hE : qPochhammer Q E k≠0) :
    basic4Term Q A B E U E F G k=basic3Term Q A B U F G k := by
  have hs : basic4Term Q A B E U E F G k=basic4Term Q A B E U F E G k := by
    unfold basic4Term
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [hs,basic4Term_cancel_middle Q A B U F E G k hE]

theorem basic4Term_cancel_last (Q A B U E F G : ℝ) (k : ℕ)
    (hG : qPochhammer Q G k≠0) :
    basic4Term Q A B G U E F G k=basic3Term Q A B U E F k := by
  have hs : basic4Term Q A B G U E F G k=basic4Term Q A B G U E G F k := by
    unfold basic4Term
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [hs,basic4Term_cancel_middle Q A B U E G F k hG]

theorem qRacahSeries_one (Q A B C D : ℝ) (n : ℕ) : qRacahSeries Q A B C D n 1=1 := by
  classical
  unfold qRacahSeries
  rw [Finset.sum_eq_single 0]
  · rw [qRacahCoefficient_zero,qRacahNewton_zero,mul_one]
  · intro k hk hk0
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    unfold qRacahNewton
    rw [inv_one,qPochhammer_cons]
    simp only [sub_self,zero_mul,mul_zero]
  · intro h
    exact (h (Finset.mem_range.mpr (by omega))).elim

end AMSPhysical

#print axioms AMSPhysical.basic4Term_cancel_middle
#print axioms AMSPhysical.qRacahSeries_one
