import QuantumMixedHomCoordinates
import QuantumCupIndependent

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
noncomputable section
namespace AMSPhysical

theorem mixedHomMatchIndex_balance (n : ℕ) (hn : 0<n) (l m h c : ℕ)
    (hadm : m≤l+c) (hRank : h=0 ∨ n=1)
    (p : MixedHomMatchIndex n hn (l+c-m+h) c l (m+h)) :
    p.val.1.val+(m:ℤ)=p.val.2.val+(c:ℤ) := by
  have he:=p.property
  have hr:=p.val.1.isLt
  have hs:=p.val.2.isLt
  have hc : (⟨0,hn⟩ : Fin n).castSucc=(0:Fin (n+1)) := Fin.ext rfl
  change mixedHighestDynkin n (l+c-m+h-p.val.1.val) (c-p.val.1.val) ⟨0,hn⟩=
    mixedHighestDynkin n (l-p.val.2.val) (m+h-p.val.2.val) ⟨0,hn⟩ at he
  simp only [mixedHighestDynkin,if_pos hc,mul_one] at he
  by_cases ht : (⟨0,hn⟩ : Fin n).succ=Fin.last n
  · simp only [if_pos ht,mul_one] at he
    omega
  · simp only [if_neg ht,mul_zero,add_zero] at he
    have hh : h=0 := by
      rcases hRank with hh|hh
      · exact hh
      · subst n
        exact False.elim (ht (Fin.ext rfl))
    omega

def cupIndexOfMixedHomMatch (n : ℕ) (hn : 0<n) (l m h c : ℕ)
    (hadm : m≤l+c) (hRank : h=0 ∨ n=1)
    (p : MixedHomMatchIndex n hn (l+c-m+h) c l (m+h)) : QuantumCupIndex l m c := by
  have hb:=mixedHomMatchIndex_balance n hn l m h c hadm hRank p
  have hr:=p.val.1.isLt
  have hs:=p.val.2.isLt
  refine ⟨⟨p.val.2.val,by omega⟩,?_⟩
  change p.val.2.val ≤ l ∧ m-p.val.2.val ≤ c
  constructor <;> omega

def mixedHomMatchOfCupIndex (n : ℕ) (hn : 0<n) (l m h c : ℕ)
    (hadm : m≤l+c) (hRank : h=0 ∨ n=1) (t : QuantumCupIndex l m c) :
    MixedHomMatchIndex n hn (l+c-m+h) c l (m+h) := by
  have ht:=t.val.isLt
  have htl:=t.property.1
  have htc:=t.property.2
  refine ⟨(⟨c-(m-t.val.val),by omega⟩,⟨t.val.val,by omega⟩),?_⟩
  change mixedHighestDynkin n (l+c-m+h-(c-(m-t.val.val))) (c-(c-(m-t.val.val))) ⟨0,hn⟩=
    mixedHighestDynkin n (l-t.val.val) (m+h-t.val.val) ⟨0,hn⟩
  have hc : (⟨0,hn⟩ : Fin n).castSucc=(0:Fin (n+1)) := Fin.ext rfl
  simp only [mixedHighestDynkin,if_pos hc,mul_one]
  by_cases hs : (⟨0,hn⟩ : Fin n).succ=Fin.last n
  · simp only [if_pos hs,mul_one]
    omega
  · simp only [if_neg hs,mul_zero,add_zero]
    have hh : h=0 := by
      rcases hRank with hh|hh
      · exact hh
      · subst n
        exact False.elim (hs (Fin.ext rfl))
    omega

/-- Exact admissible channel counting for the higher-rank Type-I space
and the shifted rank-two space, derived from actual highest weights. -/
def mixedHomCupIndexEquiv (n : ℕ) (hn : 0<n) (l m h c : ℕ)
    (hadm : m≤l+c) (hRank : h=0 ∨ n=1) :
    MixedHomMatchIndex n hn (l+c-m+h) c l (m+h) ≃ QuantumCupIndex l m c where
  toFun := cupIndexOfMixedHomMatch n hn l m h c hadm hRank
  invFun := mixedHomMatchOfCupIndex n hn l m h c hadm hRank
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      have hb:=mixedHomMatchIndex_balance n hn l m h c hadm hRank p
      have hr:=p.val.1.isLt
      change c-(m-p.val.2.val)=p.val.1.val
      omega
    · apply Fin.ext
      rfl
  right_inv t := by
    apply Subtype.ext
    apply Fin.ext
    rfl

end AMSPhysical
#print axioms AMSPhysical.mixedHomCupIndexEquiv
