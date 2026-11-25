import TwoRowRootStringsTotal
import CompactHighestChannelTransfer

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

/-- Actual compact highest transport agrees with the independent rank-two
string on ALL first-root descendants, not only on the highest vector. -/
theorem twoRowCanonicalTransport_rootString (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (S r l m l' m' : ℕ) (hS : l+m=S) (hS' : l'+m'=S)
    (hl : r≤l) (hm : r≤m) (hl' : r≤l') (hm' : r≤m')
    (v : finiteWeightSpace (K:=ℝ) (S-2*r)) :
    (CompactHighestRealization.transport (ne_of_gt hq)
      (twoRowHighestRealization q hq hq1 n hn S r l m hS hl hm)
      (twoRowHighestRealization q hq hq1 n hn S r l' m' hS' hl' hm')
      ⟨twoRowRootStringAtTotal q hq hq1 n hn S r l m hS hl hm v,
        twoRowRootStringAtTotal_mem q hq hq1 n hn S r l m hS hl hm v⟩).val=
    twoRowRootStringAtTotal q hq hq1 n hn S r l' m' hS' hl' hm' v := by
  let V:=quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m
  let W:=quantumOccupationSpace ℝ (Fin (n+1)) l' ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m'
  letI : AddCommGroup V:=inferInstance
  letI : Module ℝ V:=inferInstance
  letI : AddCommGroup W:=inferInstance
  letI : Module ℝ W:=inferInstance
  let X:=twoRowHighestRealization q hq hq1 n hn S r l m hS hl hm
  let Y:=twoRowHighestRealization q hq hq1 n hn S r l' m' hS' hl' hm'
  let T : finiteWeightSpace (K:=ℝ) (S-2*r) →ₗ[ℝ] W:=Y.channel.subtype.comp
    ((X.transport (ne_of_gt hq) Y).toLinearMap.comp
      ((twoRowRootStringAtTotal q hq hq1 n hn S r l m hS hl hm).codRestrict X.channel
        (twoRowRootStringAtTotal_mem q hq hq1 n hn S r l m hS hl hm)))
  have hF : ∀ w,T (finiteQuantumF q (S-2*r) w)=Y.action
      (typeAAlgebraGenerator q n (⟨0,hn⟩ : Fin n) 1) (T w) := by
    intro w
    change (X.transport (ne_of_gt hq) Y
      ⟨twoRowRootStringAtTotal q hq hq1 n hn S r l m hS hl hm (finiteQuantumF q (S-2*r) w),_⟩).val=_
    have he:=X.transport_intertwines (ne_of_gt hq) Y
      (typeAAlgebraGenerator q n (⟨0,hn⟩ : Fin n) 1)
      ⟨twoRowRootStringAtTotal q hq hq1 n hn S r l m hS hl hm w,
        twoRowRootStringAtTotal_mem q hq hq1 n hn S r l m hS hl hm w⟩
    simpa only [twoRowRootStringAtTotal_F] using he
  have h0 : T (standardWeightBasis (S-2*r) 0)=
      twoRowRootStringAtTotal q hq hq1 n hn S r l' m' hS' hl' hm' (standardWeightBasis (S-2*r) 0) := by
    change (X.transport (ne_of_gt hq) Y
      ⟨twoRowRootStringAtTotal q hq hq1 n hn S r l m hS hl hm (standardWeightBasis (S-2*r) 0),_⟩).val=_
    simpa only [twoRowRootStringAtTotal_highest] using X.transport_highest (ne_of_gt hq) Y
  have he:=finiteQuantumF_cyclic_unique q hq hq1 (S-2*r)
    (Y.action (typeAAlgebraGenerator q n (⟨0,hn⟩ : Fin n) 1)) T
    (twoRowRootStringAtTotal q hq hq1 n hn S r l' m' hS' hl' hm') hF
    (twoRowRootStringAtTotal_F q hq hq1 n hn S r l' m' hS' hl' hm') h0
  exact DFunLike.congr_fun he v

end AMSPhysical
#print axioms AMSPhysical.twoRowCanonicalTransport_rootString
