import GlobalVertexSigns
import QuantumMixedFusionHighest

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

def dynkinBox (n : ℕ) (lam : Fin n → ℤ) : ℤ := ∑ i,((i.val+1:ℕ):ℤ)*lam i

theorem dynkinBox_single (n : ℕ) (i : Fin n) (a : ℤ) :
    dynkinBox n (Pi.single i a)=((i.val+1:ℕ):ℤ)*a := by
  classical
  simp [dynkinBox,Pi.single_apply]

theorem dynkinBox_add (n : ℕ) (a b : Fin n → ℤ) :
    dynkinBox n (a+b)=dynkinBox n a+dynkinBox n b := by
  simp only [dynkinBox,Pi.add_apply,mul_add,Finset.sum_add_distrib]

theorem mixedHighestDynkin_as_singles (n : ℕ) (hn : 0<n) (p s : ℕ) :
    mixedHighestDynkin n p s =
      Pi.single (⟨0,hn⟩:Fin n) (p:ℤ)+Pi.single (⟨n-1,by omega⟩:Fin n) (s:ℤ) := by
  classical
  funext i
  have h0 : i.castSucc=(0:Fin (n+1)) ↔ i=(⟨0,hn⟩:Fin n) := by
    simp only [Fin.ext_iff,Fin.coe_castSucc,Fin.val_zero,Fin.val_mk]
  have hL : i.succ=Fin.last n ↔ i=(⟨n-1,by omega⟩:Fin n) := by
    simp only [Fin.ext_iff,Fin.val_succ,Fin.val_last,Fin.val_mk]
    have hi:=i.isLt
    omega
  simp only [mixedHighestDynkin,h0,hL,Pi.add_apply,Pi.single_apply]
  split_ifs <;> simp_all

theorem dynkinBox_mixed (n : ℕ) (hn : 0<n) (p s : ℕ) :
    dynkinBox n (mixedHighestDynkin n p s)=(p:ℤ)+(n:ℤ)*(s:ℤ) := by
  rw [mixedHighestDynkin_as_singles n hn,dynkinBox_add,dynkinBox_single,dynkinBox_single]
  simp only [Fin.val_mk,zero_add,Nat.cast_one,one_mul]
  have he : n-1+1=n := by omega
  rw [he]

theorem mixedHighestDynkin_pure_symmetric_iff (n : ℕ) (hn : 2≤n) (p s : ℕ) :
    (∃ a : ℕ,mixedHighestDynkin n p s=mixedHighestDynkin n a 0) ↔ s=0 := by
  constructor
  · rintro ⟨a,he⟩
    have hl : ((⟨n-1,by omega⟩:Fin n).castSucc : Fin (n+1))≠0 := by
      simp only [ne_eq,Fin.ext_iff,Fin.coe_castSucc,Fin.val_mk,Fin.val_zero]
      omega
    have hs : (⟨n-1,by omega⟩:Fin n).succ=Fin.last n := by
      simp only [Fin.ext_iff,Fin.val_succ,Fin.val_last,Fin.val_mk]
      omega
    have h:=congrArg (fun z : Fin n → ℤ=>z ⟨n-1,by omega⟩) he
    simp only [mixedHighestDynkin,if_neg hl,if_pos hs,mul_zero,mul_one,Nat.cast_zero,zero_mul,zero_add] at h
    exact_mod_cast h
  · intro he
    exact ⟨p,by rw [he]⟩

/-- An intrinsic phase depending only on the ordered actual Dynkin triple.
The determinant defect is divided by N=n+1; all relevant defects below
are proved nonnegative multiples of N. -/
def amsDynkinVertexPhase (n : ℕ) (a b c : Fin n → ℤ) : ℝ := by
  classical
  exact if ∃ p : ℕ,b=mixedHighestDynkin n p 0 then 1
    else (-1:ℝ)^((n-1)*((dynkinBox n a+dynkinBox n b-dynkinBox n c)/((n+1:ℕ):ℤ)).toNat)

theorem amsDynkinVertexPhase_square (n : ℕ) (a b c : Fin n → ℤ) :
    amsDynkinVertexPhase n a b c*amsDynkinVertexPhase n a b c=1 := by
  unfold amsDynkinVertexPhase
  split_ifs
  · norm_num
  · rw [← mul_pow]
    norm_num

def amsDynkinGlobalSigns (n : ℕ) : GlobalVertexSigns (Fin n → ℤ) where
  sign := amsDynkinVertexPhase n
  square := amsDynkinVertexPhase_square n

theorem amsDynkinVertexPhase_symmetric_second (n p : ℕ) (a c : Fin n → ℤ) :
    amsDynkinVertexPhase n a (mixedHighestDynkin n p 0) c=1 := by
  unfold amsDynkinVertexPhase
  rw [if_pos ⟨p,rfl⟩]

end AMSPhysical
#print axioms AMSPhysical.amsDynkinVertexPhase_square
