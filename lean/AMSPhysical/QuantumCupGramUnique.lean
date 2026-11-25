import BidiagonalPairGramUnique
import QuantumCupDiagonalDistinct
import QuantumCupRadialAction

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical

/-- On the independently proved cup basis, the two actual radial operators
determine every bilinear pairing from a single edge norm. -/
theorem quantumCupRadial_form_zero (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l m h c : ℕ) (hadm : m ≤ l+c)
    (H : quantumCupSpan q n l m h c →ₗ[ℝ] quantumCupSpan q n l m h c →ₗ[ℝ] ℝ)
    (hHA : PairAdjoint (V:=quantumCupSpan q n l m h c) H
      (quantumCupLeftAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m h c)
      (quantumCupLeftAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m h c))
    (hHD : PairAdjoint (V:=quantumCupSpan q n l m h c) H
      (quantumCupRightAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m h c)
      (quantumCupRightAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m h c))
    (hNorm : H (quantumCupBasis q hq n hn l m h c (quantumCupTop l m c hadm))
      (quantumCupBasis q hq n hn l m h c (quantumCupTop l m c hadm))=0) : H=0 := by
  let V := quantumCupSpan q n l m h c
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  let b : Module.Basis (QuantumCupIndex l m c) ℝ V := quantumCupBasis q hq n hn l m h c
  have hBasis (r : QuantumCupIndex l m c) :
      b r=quantumCupVector q n l m h c r :=
    quantumCupBasis_apply q hq n hn l m h c r
  apply bidiagonalPair_form_zero (V:=V) b
    (fun r : QuantumCupIndex l m c =>r.val.val)
    (by intro r s he;apply Subtype.ext;exact Fin.ext he)
    (quantumCupTop l m c hadm) (quantumCupTop_max l m c hadm)
    (fun r hr =>quantumCupRaiseLeft l m c r (quantumCup_notTop_canRaiseLeft l m c hadm r hr))
    (by intro r hr;rfl)
    (quantumCupLeftAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m h c)
    (quantumCupRightAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m h c)
    (fun r =>quantumCupLeftDiagonal q n (l:ℤ) (h:ℤ) r.val.val (m-r.val.val))
    (fun r =>quantumCupLeftOffDiagonal q n (l:ℤ) (h:ℤ) (c:ℤ) r.val.val (m-r.val.val))
    (fun r =>quantumCupLeftDiagonal q n (c:ℤ) (h:ℤ) (m-r.val.val-1) (r.val.val+1))
    (fun r =>quantumCupLeftOffDiagonal q n (c:ℤ) (h:ℤ) (l:ℤ) (m-r.val.val-1) (r.val.val+1))
    _ _ _ _ _ H hHA hHD hNorm
  · have hs : ¬quantumCupCanRaiseLeft l m c (quantumCupTop l m c hadm) := by
      unfold quantumCupCanRaiseLeft quantumCupTop
      simp only
      omega
    simp only [hBasis]
    rw [quantumCupLeftAction_vector,dif_neg hs,add_zero]
  · intro r hr
    simp only [hBasis]
    rw [quantumCupLeftAction_vector,dif_pos (quantumCup_notTop_canRaiseLeft l m c hadm r hr)]
  · intro r hr
    exact quantumCupLeftDiagonal_top_ne q hq hq1 n hn l m h c hadm r hr
  · intro r hr
    let hs:=quantumCup_notTop_canRaiseLeft l m c hadm r hr
    simp only [hBasis]
    rw [quantumCupRightAction_vector,dif_pos (quantumCup_raisedLeft_canRaiseRight l m c r hs),
      quantumCup_raiseRight_raiseLeft,quantumCupRaiseLeft_rightCount]
    rfl
  · intro r hr
    let hs:=quantumCup_notTop_canRaiseLeft l m c hadm r hr
    have hz:=quantumCupRightOffDiagonal_nonzero q hq hq1 n l m h c (quantumCupRaiseLeft l m c r hs)
      (quantumCup_raisedLeft_canRaiseRight l m c r hs)
    rw [quantumCupRaiseLeft_rightCount] at hz
    exact hz

end AMSPhysical
#print axioms AMSPhysical.quantumCupRadial_form_zero
