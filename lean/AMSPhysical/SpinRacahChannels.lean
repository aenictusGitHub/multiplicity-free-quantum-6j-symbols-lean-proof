import SpinRacahEndpoints
import QuantumChannelNeighbors
import QuantumRacahRates
import QuantumBoundaryRecoupling

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
noncomputable section
namespace AMSPhysical

theorem fixedLeftHighest_minimum_bound (l m n H : ℕ) (p : FixedLeftHighest l m n H) :
    leftHighestDefect l m n H-n≤p.val.1.val := by
  have hd := fixedLeftHighest_defect l m n H p
  have hn := channel_right_bound (coupledLabel l m p.val.1) n p.val.2
  omega

theorem fixedLeftHighest_boundary_index (l m n H : ℕ) (p : FixedLeftHighest l m n H)
    (hb : p.val.1.val=0 ∨ p.val.2.val=n) :
    p.val.1.val=leftHighestDefect l m n H-n := by
  have hd := fixedLeftHighest_defect l m n H p
  have hn := channel_right_bound (coupledLabel l m p.val.1) n p.val.2
  rcases hb with hr | hs <;> omega

theorem fixedLeftHighest_successor (l m n H : ℕ) (p : FixedLeftHighest l m n H)
    (hl : p.val.1.val<l) (hm : p.val.1.val<m)
    (hs : 0<p.val.2.val) (hi : p.val.2.val<coupledLabel l m p.val.1) :
    ∃ v : FixedLeftHighest l m n H,p.val.1.val+1=v.val.1.val := by
  have hn := channel_right_bound (coupledLabel l m p.val.1) n p.val.2
  let r : Fin (min l m+1) := ⟨p.val.1.val+1,by omega⟩
  have hib : p.val.2.val-1≤coupledLabel l m r := by
    dsimp [r]
    unfold coupledLabel at *
    omega
  let s : Fin (min (coupledLabel l m r) n+1) := ⟨p.val.2.val-1,
    Nat.lt_succ_iff.mpr (le_min hib (by omega))⟩
  let a : LeftHighestPath l m n := ⟨r,s⟩
  have ht : leftTotalLabel l m n a=H := by
    have h₁ := leftTotalLabel_defect l m n p.val
    have h₂ := leftTotalLabel_defect l m n a
    rw [p.property] at h₁
    change l+m+n=leftTotalLabel l m n a+2*((p.val.1.val+1)+(p.val.2.val-1)) at h₂
    omega
  exact ⟨⟨a,ht⟩,rfl⟩

theorem rightHighest_spinRacah_admissible (l m n H : ℕ) (a : RightHighestPath l m n)
    (hH : rightTotalLabel l m n a=H) :
    SpinRacahAdmissible l m n (leftHighestDefect l m n H) a.1.val := by
  have hu := channel_left_bound m n a.1
  have hun := channel_right_bound m n a.1
  have hv := channel_left_bound l (coupledLabel m n a.1) a.2
  have hvj := channel_right_bound l (coupledLabel m n a.1) a.2
  have hd := rightTotalLabel_defect l m n a
  rw [hH] at hd
  have hR : a.1.val+a.2.val=leftHighestDefect l m n H := by
    unfold leftHighestDefect
    omega
  have hj : coupledLabel m n a.1=m+n-2*a.1.val := rfl
  exact ⟨hu,hun,by omega,by omega,by omega⟩

theorem sl2RacahDeath_lower_boundary (q : ℝ) (l m n H : ℕ)
    (p : FixedLeftHighest l m n H)
    (hp : ¬∃ v : FixedLeftHighest l m n H,v.val.1.val+1=p.val.1.val) :
    sl2RacahDeath q l m n p.val.1.val p.val.2.val=0 := by
  have hn := channel_right_bound (coupledLabel l m p.val.1) n p.val.2
  have hb : p.val.1.val=0 ∨ p.val.2.val=n := by
    by_contra h
    exact hp (fixedLeftHighest_previous l m n H p (by omega) (by omega))
  unfold sl2RacahDeath
  rcases hb with hr | hs
  · have hrc : (p.val.1.val:ℤ)=0 := by omega
    simp only [hrc,qInteger_zero,mul_zero,zero_mul,zero_div]
  · have hsc : (n:ℤ)-(p.val.2.val:ℤ)=0 := by omega
    simp only [hsc,qInteger_zero,mul_zero,zero_mul,zero_div]

theorem spinRacah_upper_boundary (Q : ℝ) (hQ : 0<Q) (hQ1 : Q≠1)
    (q : ℝ) (l m n H u : ℕ)
    (h : SpinRacahAdmissible l m n (leftHighestDefect l m n H) u)
    (p : FixedLeftHighest l m n H)
    (hp : ¬∃ v : FixedLeftHighest l m n H,p.val.1.val+1=v.val.1.val) :
    sl2RacahBirth q l m n p.val.1.val p.val.2.val*
      spinRacahFunction Q l m n (leftHighestDefect l m n H) u ((p.val.1.val:ℤ)+1)=0 := by
  have hl := channel_left_bound l m p.val.1
  have hm := channel_right_bound l m p.val.1
  have hi := channel_left_bound (coupledLabel l m p.val.1) n p.val.2
  have hd := fixedLeftHighest_defect l m n H p
  have hb : p.val.1.val=l ∨ p.val.1.val=m ∨ p.val.2.val=0 ∨ p.val.2.val=coupledLabel l m p.val.1 := by
    by_contra hh
    exact hp (fixedLeftHighest_successor l m n H p (by omega) (by omega) (by omega) (by omega))
  by_cases hzero : p.val.1.val=m ∨ p.val.2.val=0
  · have hz : sl2RacahBirth q l m n p.val.1.val p.val.2.val=0 := by
      unfold sl2RacahBirth
      rcases hzero with hr | hs
      · have hrc : (m:ℤ)-(p.val.1.val:ℤ)=0 := by omega
        simp only [hrc,qInteger_zero,mul_zero,zero_mul,zero_div]
      · have hsc : (p.val.2.val:ℤ)=0 := by omega
        simp only [hsc,qInteger_zero,mul_zero,zero_mul,zero_div]
    rw [hz,zero_mul]
  · have hz : spinRacahFunction Q l m n (leftHighestDefect l m n H) u ((p.val.1.val:ℤ)+1)=0 := by
      rcases hb with hr | hr | hs | hs
      · have hrc : (p.val.1.val:ℤ)=(l:ℤ) := by omega
        rw [hrc]
        exact spinRacah_virtual_left_zero Q hQ hQ1 l m n _ u h (by omega)
      · exact False.elim (hzero (Or.inl hr))
      · exact False.elim (hzero (Or.inr hs))
      · have hindex : (p.val.1.val:ℤ)+1=(l:ℤ)+(m:ℤ)-(leftHighestDefect l m n H:ℤ)+1 := by
          unfold coupledLabel at hs
          omega
        rw [hindex]
        apply spinRacah_virtual_reflected_zero Q hQ hQ1 l m n _ u h
        unfold coupledLabel at hs
        omega
    rw [hz,mul_zero]

end AMSPhysical

#print axioms AMSPhysical.rightHighest_spinRacah_admissible
#print axioms AMSPhysical.spinRacah_upper_boundary
