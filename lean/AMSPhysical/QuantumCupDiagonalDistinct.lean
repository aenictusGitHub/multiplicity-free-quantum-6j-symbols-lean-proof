import QuantumCenteredProduct
import QuantumCupTop

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical

def quantumCupLeftEigenvalue (q : ℝ) (n l m h t : ℕ) : ℝ :=
  q^(-(l:ℤ)-(h:ℤ)-(m:ℤ)-(n:ℤ)+2)*qInteger q (t:ℤ)*
    qInteger q ((l:ℤ)+(h:ℤ)+(m:ℤ)+(n:ℤ)-(t:ℤ))

theorem quantumCupLeftDiagonal_fixed (q : ℝ) (n l m h t : ℕ) (ht : t ≤ m) :
    quantumCupLeftDiagonal q n (l:ℤ) (h:ℤ) t (m-t)=quantumCupLeftEigenvalue q n l m h t := by
  unfold quantumCupLeftDiagonal quantumCupLeftEigenvalue
  rw [Nat.cast_sub ht]
  have he : -(l:ℤ)-(h:ℤ)-(t:ℤ)-((m:ℤ)-(t:ℤ))-(n:ℤ)+2=
      -(l:ℤ)-(h:ℤ)-(m:ℤ)-(n:ℤ)+2 := by ring
  have he' : (l:ℤ)+(h:ℤ)+((m:ℤ)-(t:ℤ))+(n:ℤ)=
      (l:ℤ)+(h:ℤ)+(m:ℤ)+(n:ℤ)-(t:ℤ) := by ring
  rw [he,he']

theorem quantumCupLeftEigenvalue_strict (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m h a b : ℕ) (hba : b < a) (hal : a ≤ l) (ham : a ≤ m) :
    quantumCupLeftEigenvalue q n l m h b < quantumCupLeftEigenvalue q n l m h a := by
  apply sub_pos.mp
  have he : quantumCupLeftEigenvalue q n l m h a-quantumCupLeftEigenvalue q n l m h b=
      q^(-(l:ℤ)-(h:ℤ)-(m:ℤ)-(n:ℤ)+2)*
        (qInteger q ((a:ℤ)-(b:ℤ))*qInteger q ((l:ℤ)+(h:ℤ)+(m:ℤ)+(n:ℤ)-(a:ℤ)-(b:ℤ))) := by
    unfold quantumCupLeftEigenvalue
    calc
      _ = q^(-(l:ℤ)-(h:ℤ)-(m:ℤ)-(n:ℤ)+2)*
        (qInteger q (a:ℤ)*qInteger q ((l:ℤ)+(h:ℤ)+(m:ℤ)+(n:ℤ)-(a:ℤ))-
          qInteger q (b:ℤ)*qInteger q ((l:ℤ)+(h:ℤ)+(m:ℤ)+(n:ℤ)-(b:ℤ))) := by ring
      _ = _ := by rw [qInteger_centered_product_difference q (ne_of_gt hq)]
  rw [he]
  apply mul_pos (zpow_pos hq _)
  apply mul_pos
  · exact qInteger_pos_real q hq hq1 _ (by omega)
  · exact qInteger_pos_real q hq hq1 _ (by omega)

theorem quantumCupLeftDiagonal_top_ne (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m h c : ℕ) (hadm : m ≤ l+c) (r : QuantumCupIndex l m c)
    (hr : r≠quantumCupTop l m c hadm) :
    quantumCupLeftDiagonal q n (l:ℤ) (h:ℤ) (quantumCupTop l m c hadm).val.val (m-(quantumCupTop l m c hadm).val.val)≠
      quantumCupLeftDiagonal q n (l:ℤ) (h:ℤ) r.val.val (m-r.val.val) := by
  have ht : (quantumCupTop l m c hadm).val.val=min l m := rfl
  have hrt : r.val.val < min l m := by
    have hmax:=quantumCupTop_max l m c hadm r
    have hne : r.val.val≠min l m := by intro he;apply hr;apply Subtype.ext;exact Fin.ext he
    rw [ht] at hmax
    omega
  have hrm : r.val.val ≤ m := by have h0:=r.val.isLt;omega
  rw [quantumCupLeftDiagonal_fixed q n l m h _ (by rw [ht];omega),quantumCupLeftDiagonal_fixed q n l m h _ hrm]
  exact ne_of_gt (quantumCupLeftEigenvalue_strict q hq hq1 n hn l m h _ _ (by rw [ht];exact hrt) (by rw [ht];omega) (by rw [ht];omega))

end AMSPhysical
