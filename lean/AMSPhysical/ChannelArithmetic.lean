import Mathlib.Tactic
set_option autoImplicit false
namespace AMSPhysical

def mixedEigen (a b n u : ℤ) : ℤ := u*(a+b+n-u-1)
def sameEigen (a b t : ℤ) : ℤ := a*b-t*(a+b-t+1)

theorem mixedEigen_strict (a b n u v : ℤ) (hn : 2≤n)
    (huv : u<v) (hva : v≤a) (hvb : v≤b) :
    mixedEigen a b n u < mixedEigen a b n v := by
  have hd : 0<v-u := by omega
  have hc : 0<a+b+n-u-v-1 := by omega
  have hp := mul_pos hd hc
  dsimp [mixedEigen]
  nlinarith

theorem sameEigen_strict (a b u v : ℤ) (huv : u<v)
    (hva : v≤a) (hvb : v≤b) : sameEigen a b v < sameEigen a b u := by
  have hd : 0<v-u := by omega
  have hc : 0<a+b-u-v+1 := by omega
  have hp := mul_pos hd hc
  dsimp [sameEigen]
  nlinarith

theorem mixedEigen_rank_shift (a b h u : ℤ) :
    mixedEigen a (b+h) 2 u=mixedEigen a b (h+2) u := by
  unfold mixedEigen
  ring

theorem sameEigen_rank_shift (a b h t : ℤ) :
    sameEigen (a+h) (b+h) (t+h)=sameEigen a b t-h := by
  unfold sameEigen
  ring

theorem mixed_channel_shift (a b u h : ℤ) : a+(b+h)-2*u=(a+b-2*u)+h := by ring
theorem same_channel_shift (a b t h : ℤ) : (a+h)+(b+h)-2*(t+h)=a+b-2*t := by ring

end AMSPhysical
#print axioms AMSPhysical.mixedEigen_strict
#print axioms AMSPhysical.sameEigen_rank_shift
