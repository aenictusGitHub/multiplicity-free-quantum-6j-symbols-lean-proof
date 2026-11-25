import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Intervals

set_option autoImplicit false

namespace AMSGeneral
open Finset

variable {𝕂 : Type*} [Field 𝕂]

/-- The six factorial offsets in AMS (35). -/
@[ext] structure Offsets where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  e : ℤ
  f : ℤ
  deriving DecidableEq

def rho (r₁ r₂ r₃ r₄ : ℤ) : ℤ := (r₁+r₂+r₃+r₄)/2

/-- h=N-2. False denotes Type I; true denotes Type II. -/
def offsets (h : ℤ) (typeII : Bool) (r₁ r₂ r₃ r₄ i j : ℤ) : Offsets where
  a := (r₃+r₄-i)/2
  b := (r₁+r₂-i)/2 + if typeII then h else 0
  c := (r₂+r₃-j)/2
  d := (r₁+r₄-j)/2
  e := (i+j-r₂-r₄)/2
  f := (i+j-r₁-r₃)/2 + if typeII then 0 else h

def support (o : Offsets) : Finset ℤ :=
  Icc (max 0 (max (-o.e) (-o.f))) (min o.a (min o.b (min o.c o.d)))

/-- The factorial function is arbitrary. In applications F(k)=[k]_q!.
No hypothesis that F already computes a 6j symbol occurs anywhere. -/
def series (F : ℤ → 𝕂) (phase top : ℤ) (o : Offsets) : 𝕂 :=
  ∑ u ∈ support o, (-1:𝕂)^(phase-u) * F (top-u) /
    (F u * F (o.a-u) * F (o.b-u) * F (o.c-u) * F (o.d-u) *
      F (o.e+u) * F (o.f+u))

def kernel (F : ℤ → 𝕂) (h : ℕ) (typeII : Bool) (r₁ r₂ r₃ r₄ i j : ℤ) : 𝕂 :=
  series F (rho r₁ r₂ r₃ r₄) (rho r₁ r₂ r₃ r₄+h+1)
    (offsets h typeII r₁ r₂ r₃ r₄ i j)

theorem series_phase (F : ℤ → 𝕂) (phase top : ℤ) (o : Offsets) (h : ℕ) :
    series F (phase+h) top o = (-1:𝕂)^h * series F phase top o := by
  unfold series
  rw [mul_sum]
  apply sum_congr rfl
  intro u hu
  have he : phase+(h:ℤ)-u = (h:ℤ)+(phase-u) := by ring
  rw [he, zpow_add₀ (by norm_num : (-1:𝕂) ≠ 0)]
  simp only [zpow_natCast]
  ring

theorem rho_typeI (h r₁ r₂ r₃ r₄ : ℤ) :
    rho r₁ (r₂+h) r₃ (r₄+h) = rho r₁ r₂ r₃ r₄+h := by
  unfold rho
  omega

theorem rho_typeII (h r₁ r₂ r₃ r₄ : ℤ) :
    rho (r₁+h) (r₂+h) r₃ r₄ = rho r₁ r₂ r₃ r₄+h := by
  unfold rho
  omega

theorem offsets_typeI (h r₁ r₂ r₃ r₄ i j : ℤ) :
    offsets 0 false r₁ (r₂+h) r₃ (r₄+h) (i+h) (j+h) =
      offsets h false r₁ r₂ r₃ r₄ i j := by
  apply Offsets.ext <;> simp only [offsets, Bool.false_eq_true, if_false] <;> omega

theorem offsets_typeII (h r₁ r₂ r₃ r₄ i j : ℤ) :
    offsets 0 true (r₁+h) (r₂+h) r₃ r₄ i (j+h) =
      offsets h true r₁ r₂ r₃ r₄ i j := by
  apply Offsets.ext <;> simp only [offsets, if_true] <;> omega

theorem shifted_kernel_typeI (F : ℤ → 𝕂) (h : ℕ) (r₁ r₂ r₃ r₄ i j : ℤ) :
    kernel F 0 false r₁ (r₂+h) r₃ (r₄+h) (i+h) (j+h) =
      (-1:𝕂)^h * kernel F h false r₁ r₂ r₃ r₄ i j := by
  unfold kernel
  simp only [Nat.cast_zero, add_zero]
  rw [rho_typeI, offsets_typeI]
  exact series_phase F (rho r₁ r₂ r₃ r₄) (rho r₁ r₂ r₃ r₄+h+1) _ h

theorem shifted_kernel_typeII (F : ℤ → 𝕂) (h : ℕ) (r₁ r₂ r₃ r₄ i j : ℤ) :
    kernel F 0 true (r₁+h) (r₂+h) r₃ r₄ i (j+h) =
      (-1:𝕂)^h * kernel F h true r₁ r₂ r₃ r₄ i j := by
  unfold kernel
  simp only [Nat.cast_zero, add_zero]
  rw [rho_typeII, offsets_typeII]
  exact series_phase F (rho r₁ r₂ r₃ r₄) (rho r₁ r₂ r₃ r₄+h+1) _ h

theorem sign_square (h : ℕ) : (-1:𝕂)^h * (-1:𝕂)^h = 1 := by
  rw [← mul_pow]
  norm_num

/-- Generic Type-I rank reduction, for any factorial function and all labels. -/
theorem rank_shift_typeI (F : ℤ → 𝕂) (h : ℕ) (r₁ r₂ r₃ r₄ i j : ℤ) :
    kernel F h false r₁ r₂ r₃ r₄ i j =
      (-1:𝕂)^h * kernel F 0 false r₁ (r₂+h) r₃ (r₄+h) (i+h) (j+h) := by
  rw [shifted_kernel_typeI, ← mul_assoc, sign_square, one_mul]

/-- Generic Type-II rank reduction, for any factorial function and all labels. -/
theorem rank_shift_typeII (F : ℤ → 𝕂) (h : ℕ) (r₁ r₂ r₃ r₄ i j : ℤ) :
    kernel F h true r₁ r₂ r₃ r₄ i j =
      (-1:𝕂)^h * kernel F 0 true (r₁+h) (r₂+h) r₃ r₄ i (j+h) := by
  rw [shifted_kernel_typeII, ← mul_assoc, sign_square, one_mul]

/-- Restoring any nonzero rank-two normalization; no 6j interpretation is assumed. -/
theorem normalized_typeI (F : ℤ → 𝕂) (h : ℕ) (r₁ r₂ r₃ r₄ i j : ℤ)
    (Kₙ K₂ : 𝕂) (hK₂ : K₂ ≠ 0) :
    Kₙ * kernel F h false r₁ r₂ r₃ r₄ i j =
      (-1:𝕂)^h * (Kₙ/K₂) *
        (K₂ * kernel F 0 false r₁ (r₂+h) r₃ (r₄+h) (i+h) (j+h)) := by
  rw [rank_shift_typeI]
  field_simp [hK₂]

theorem normalized_typeII (F : ℤ → 𝕂) (h : ℕ) (r₁ r₂ r₃ r₄ i j : ℤ)
    (Kₙ K₂ : 𝕂) (hK₂ : K₂ ≠ 0) :
    Kₙ * kernel F h true r₁ r₂ r₃ r₄ i j =
      (-1:𝕂)^h * (Kₙ/K₂) *
        (K₂ * kernel F 0 true (r₁+h) (r₂+h) r₃ r₄ i (j+h)) := by
  rw [rank_shift_typeII]
  field_simp [hK₂]

end AMSGeneral

#print axioms AMSGeneral.rank_shift_typeI
#print axioms AMSGeneral.rank_shift_typeII
#print axioms AMSGeneral.normalized_typeI
#print axioms AMSGeneral.normalized_typeII
#check AMSGeneral.rank_shift_typeI
#check AMSGeneral.rank_shift_typeII
