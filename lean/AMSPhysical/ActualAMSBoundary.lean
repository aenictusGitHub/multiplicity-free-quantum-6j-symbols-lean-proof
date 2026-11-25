import ActualAMSCarriers
import HighestFunctionalCartan
import OccupationCartanLine
import AMSDynkinVertexPhase

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

theorem mixedHighestDynkin_first (n : ℕ) (hn : 2≤n) (p s : ℕ) :
    mixedHighestDynkin n p s ⟨0,by omega⟩=(p:ℤ) := by
  have hL : (⟨0,by omega⟩:Fin n).succ≠Fin.last n := by
    simp only [ne_eq,Fin.ext_iff,Fin.val_succ,Fin.val_mk,Fin.val_last];omega
  unfold mixedHighestDynkin
  rw [if_pos (show (⟨0,by omega⟩:Fin n).castSucc=(0:Fin (n+1)) from rfl),if_neg hL]
  ring

theorem mixedHighestDynkin_last (n : ℕ) (hn : 2≤n) (p s : ℕ) :
    mixedHighestDynkin n p s ⟨n-1,by omega⟩=(s:ℤ) := by
  have h0 : (⟨n-1,by omega⟩:Fin n).castSucc≠(0:Fin (n+1)) := by
    simp only [ne_eq,Fin.ext_iff,Fin.val_mk,Fin.coe_castSucc,Fin.val_zero];omega
  have hL : (⟨n-1,by omega⟩:Fin n).succ=Fin.last n := by
    simp only [Fin.ext_iff,Fin.val_succ,Fin.val_mk,Fin.val_last];omega
  unfold mixedHighestDynkin
  rw [if_neg h0,if_pos hL]
  ring

theorem mixedHighestDynkin_parameters (n : ℕ) (hn : 2≤n) (p s a b : ℕ)
    (he : mixedHighestDynkin n p s=mixedHighestDynkin n a b) : p=a ∧ s=b := by
  have hf:=congrArg (fun w : Fin n → ℤ=>w ⟨0,by omega⟩) he
  have hl:=congrArg (fun w : Fin n → ℤ=>w ⟨n-1,by omega⟩) he
  dsimp only at hf hl
  rw [mixedHighestDynkin_first n hn,mixedHighestDynkin_first n hn] at hf
  rw [mixedHighestDynkin_last n hn,mixedHighestDynkin_last n hn] at hl
  exact ⟨by exact_mod_cast hf,by exact_mod_cast hl⟩

def actualBoundaryFrom {q : ℝ} {n : ℕ} (hq : q≠0) (A : ActualIrrep q n)
    {lam : Fin n → ℤ} (C : ActualHighestCarrier q n lam) (he : A.val=lam)
    (f : C.space →ₗ[ℝ] ℝ) : (fixedActualCarrier A).space →ₗ[ℝ] ℝ := by
  subst lam
  exact f.comp ((fixedActualCarrier A).mapTo hq C)

theorem actualBoundaryFrom_roundtrip {q : ℝ} {n : ℕ} {lam : Fin n → ℤ} (hq : q≠0)
    (C : ActualHighestCarrier q n lam) (f : C.space →ₗ[ℝ] ℝ) (v : C.space) :
    actualBoundaryFrom hq C.irrep C rfl f (C.mapTo hq (fixedActualCarrier C.irrep) v)=f v := by
  change f (((fixedActualCarrier C.irrep).mapTo hq C).comp (C.mapTo hq (fixedActualCarrier C.irrep)) v)=_
  rw [C.mapTo_comp,C.mapTo_self,LinearMap.id_apply]

def amsActualBoundary (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 2≤n)
    (A : ActualIrrep q n) : (fixedActualCarrier A).space →ₗ[ℝ] ℝ := by
  classical
  exact if hS : ∃ p : ℕ,A.val=mixedHighestDynkin n p 0 then
      actualBoundaryFrom (ne_of_gt hq) A (actualSymmetricCarrier q hq hq1 n (Classical.choose hS))
        (Classical.choose_spec hS) (occupationAugmentation n (Classical.choose hS))
    else if hO : ∃ s : ℕ,A.val=mixedHighestDynkin n 0 s then
      actualBoundaryFrom (ne_of_gt hq) A (actualOppositeCarrier q hq hq1 n (by omega) (Classical.choose hO))
        (Classical.choose_spec hO) (occupationAugmentation n (Classical.choose hO))
    else if hM : ∃ p s : ℕ,A.val=mixedHighestDynkin n p s then
      let p:=Classical.choose hM
      let s:=Classical.choose (Classical.choose_spec hM)
      actualBoundaryFrom (ne_of_gt hq) A (actualMixedCarrier q hq hq1 n (by omega) p s)
        (Classical.choose_spec (Classical.choose_spec hM))
        ((mixedFirstBoundaryFunctional n p s).comp
          (globalMixedPairRealization q hq hq1 n (by omega) p s 0).channel.subtype)
    else 0

theorem actualBoundaryFrom_symmetric_degree (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 2≤n)
    (p a : ℕ) (he : mixedHighestDynkin n p 0=mixedHighestDynkin n a 0)
    (v : (actualSymmetricCarrier q hq hq1 n p).space) :
    actualBoundaryFrom (ne_of_gt hq) (actualSymmetricCarrier q hq hq1 n p).irrep
      (actualSymmetricCarrier q hq hq1 n a) he (occupationAugmentation n a)
      ((actualSymmetricCarrier q hq hq1 n p).mapTo (ne_of_gt hq)
        (fixedActualCarrier (actualSymmetricCarrier q hq hq1 n p).irrep) v)=occupationAugmentation n p v := by
  have ha : p=a:=(mixedHighestDynkin_parameters n hn p 0 a 0 he).1
  subst a
  exact actualBoundaryFrom_roundtrip (ne_of_gt hq) (actualSymmetricCarrier q hq hq1 n p)
    (occupationAugmentation n p) v

theorem amsActualBoundary_symmetric (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 2≤n)
    (p : ℕ) (v : (actualSymmetricCarrier q hq hq1 n p).space) :
    amsActualBoundary q hq hq1 n hn (actualSymmetricCarrier q hq hq1 n p).irrep
      ((actualSymmetricCarrier q hq hq1 n p).mapTo (ne_of_gt hq)
        (fixedActualCarrier (actualSymmetricCarrier q hq hq1 n p).irrep) v) = occupationAugmentation n p v := by
  classical
  have hS : ∃ a : ℕ,(actualSymmetricCarrier q hq hq1 n p).irrep.val=mixedHighestDynkin n a 0:=⟨p,rfl⟩
  unfold amsActualBoundary
  rw [dif_pos hS]
  exact actualBoundaryFrom_symmetric_degree q hq hq1 n hn p (Classical.choose hS) (Classical.choose_spec hS) v

theorem actualBoundaryFrom_opposite_degree (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 2≤n)
    (s b : ℕ) (he : mixedHighestDynkin n 0 s=mixedHighestDynkin n 0 b)
    (v : (actualOppositeCarrier q hq hq1 n (by omega) s).space) :
    actualBoundaryFrom (ne_of_gt hq) (actualOppositeCarrier q hq hq1 n (by omega) s).irrep
      (actualOppositeCarrier q hq hq1 n (by omega) b) he (occupationAugmentation n b)
      ((actualOppositeCarrier q hq hq1 n (by omega) s).mapTo (ne_of_gt hq)
        (fixedActualCarrier (actualOppositeCarrier q hq hq1 n (by omega) s).irrep) v)=occupationAugmentation n s v := by
  have hb : s=b:=(mixedHighestDynkin_parameters n hn 0 s 0 b he).2
  subst b
  exact actualBoundaryFrom_roundtrip (ne_of_gt hq) (actualOppositeCarrier q hq hq1 n (by omega) s)
    (occupationAugmentation n s) v

theorem amsActualBoundary_opposite_positive_degree (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 2≤n)
    (s : ℕ) (hs : 0<s) (v : (actualOppositeCarrier q hq hq1 n (by omega) s).space) :
    amsActualBoundary q hq hq1 n hn (actualOppositeCarrier q hq hq1 n (by omega) s).irrep
      ((actualOppositeCarrier q hq hq1 n (by omega) s).mapTo (ne_of_gt hq)
        (fixedActualCarrier (actualOppositeCarrier q hq hq1 n (by omega) s).irrep) v)=occupationAugmentation n s v := by
  classical
  have hS : ¬∃ p : ℕ,(actualOppositeCarrier q hq hq1 n (by omega) s).irrep.val=mixedHighestDynkin n p 0 := by
    rintro ⟨p,hp⟩
    have he:=(mixedHighestDynkin_parameters n hn 0 s p 0 hp).2
    omega
  have hO : ∃ b : ℕ,(actualOppositeCarrier q hq hq1 n (by omega) s).irrep.val=mixedHighestDynkin n 0 b:=⟨s,rfl⟩
  unfold amsActualBoundary
  rw [dif_neg hS,dif_pos hO]
  exact actualBoundaryFrom_opposite_degree q hq hq1 n hn s (Classical.choose hO) (Classical.choose_spec hO) v

theorem actualBoundaryFrom_mixed_parameters (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 2≤n)
    (p s a b : ℕ) (he : mixedHighestDynkin n p s=mixedHighestDynkin n a b)
    (v : (actualMixedCarrier q hq hq1 n (by omega) p s).space) :
    actualBoundaryFrom (ne_of_gt hq) (actualMixedCarrier q hq hq1 n (by omega) p s).irrep
      (actualMixedCarrier q hq hq1 n (by omega) a b) he
      ((mixedFirstBoundaryFunctional n a b).comp
        (globalMixedPairRealization q hq hq1 n (by omega) a b 0).channel.subtype)
      ((actualMixedCarrier q hq hq1 n (by omega) p s).mapTo (ne_of_gt hq)
        (fixedActualCarrier (actualMixedCarrier q hq hq1 n (by omega) p s).irrep) v)=
      mixedFirstBoundaryFunctional n p s v.val := by
  obtain ⟨ha,hb⟩:=mixedHighestDynkin_parameters n hn p s a b he
  subst a
  subst b
  exact actualBoundaryFrom_roundtrip (ne_of_gt hq) (actualMixedCarrier q hq hq1 n (by omega) p s) _ v

theorem amsActualBoundary_mixed_positive_parameters (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 2≤n)
    (p s : ℕ) (hp : 0<p) (hs : 0<s) (v : (actualMixedCarrier q hq hq1 n (by omega) p s).space) :
    amsActualBoundary q hq hq1 n hn (actualMixedCarrier q hq hq1 n (by omega) p s).irrep
      ((actualMixedCarrier q hq hq1 n (by omega) p s).mapTo (ne_of_gt hq)
        (fixedActualCarrier (actualMixedCarrier q hq hq1 n (by omega) p s).irrep) v)=
      mixedFirstBoundaryFunctional n p s v.val := by
  classical
  have hS : ¬∃ a : ℕ,(actualMixedCarrier q hq hq1 n (by omega) p s).irrep.val=mixedHighestDynkin n a 0 := by
    rintro ⟨a,ha⟩
    have he:=(mixedHighestDynkin_parameters n hn p s a 0 ha).2
    omega
  have hO : ¬∃ b : ℕ,(actualMixedCarrier q hq hq1 n (by omega) p s).irrep.val=mixedHighestDynkin n 0 b := by
    rintro ⟨b,hb⟩
    have he:=(mixedHighestDynkin_parameters n hn p s 0 b hb).1
    omega
  have hM : ∃ a b : ℕ,(actualMixedCarrier q hq hq1 n (by omega) p s).irrep.val=mixedHighestDynkin n a b:=⟨p,s,rfl⟩
  unfold amsActualBoundary
  rw [dif_neg hS,dif_neg hO,dif_pos hM]
  exact actualBoundaryFrom_mixed_parameters q hq hq1 n hn p s _ _
    (Classical.choose_spec (Classical.choose_spec hM)) v

theorem amsActualBoundary_opposite_zero (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 2≤n)
    (v : (actualOppositeCarrier q hq hq1 n (by omega) 0).space) :
    amsActualBoundary q hq hq1 n hn (actualOppositeCarrier q hq hq1 n (by omega) 0).irrep
      ((actualOppositeCarrier q hq hq1 n (by omega) 0).mapTo (ne_of_gt hq)
        (fixedActualCarrier (actualOppositeCarrier q hq hq1 n (by omega) 0).irrep) v)=occupationAugmentation n 0 v := by
  have hH : amsActualBoundary q hq hq1 n hn (actualOppositeCarrier q hq hq1 n (by omega) 0).irrep
      (fixedActualCarrier (actualOppositeCarrier q hq hq1 n (by omega) 0).irrep).frame.highest=1 := by
    have hh:=amsActualBoundary_symmetric q hq hq1 n hn 0
      (actualSymmetricCarrier q hq hq1 n 0).frame.highest
    rw [ActualHighestCarrier.mapTo_highest] at hh
    exact hh.trans (occupationAugmentation_basis n 0 (highestOccupation n 0))
  have he : (amsActualBoundary q hq hq1 n hn (actualOppositeCarrier q hq hq1 n (by omega) 0).irrep).comp
      ((actualOppositeCarrier q hq hq1 n (by omega) 0).mapTo (ne_of_gt hq)
        (fixedActualCarrier (actualOppositeCarrier q hq hq1 n (by omega) 0).irrep))=occupationAugmentation n 0 := by
    apply (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) 0).ext
    intro x
    have hx : x=lowestOccupation n 0 :=
      (zeroOccupation_unique n x).trans (zeroOccupation_unique n (lowestOccupation n 0)).symm
    rw [hx]
    change amsActualBoundary q hq hq1 n hn (actualOppositeCarrier q hq hq1 n (by omega) 0).irrep
      ((actualOppositeCarrier q hq hq1 n (by omega) 0).mapTo (ne_of_gt hq)
        (fixedActualCarrier (actualOppositeCarrier q hq hq1 n (by omega) 0).irrep)
        (actualOppositeCarrier q hq hq1 n (by omega) 0).frame.highest)=_
    rw [ActualHighestCarrier.mapTo_highest,hH,occupationAugmentation_basis]
  exact DFunLike.congr_fun he v

theorem amsActualBoundary_opposite (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 2≤n)
    (s : ℕ) (v : (actualOppositeCarrier q hq hq1 n (by omega) s).space) :
    amsActualBoundary q hq hq1 n hn (actualOppositeCarrier q hq hq1 n (by omega) s).irrep
      ((actualOppositeCarrier q hq hq1 n (by omega) s).mapTo (ne_of_gt hq)
        (fixedActualCarrier (actualOppositeCarrier q hq hq1 n (by omega) s).irrep) v)=occupationAugmentation n s v := by
  by_cases hs : s=0
  · subst s
    exact amsActualBoundary_opposite_zero q hq hq1 n hn v
  · exact amsActualBoundary_opposite_positive_degree q hq hq1 n hn s (by omega) v

end AMSPhysical
#print axioms AMSPhysical.amsActualBoundary_symmetric
#print axioms AMSPhysical.amsActualBoundary_mixed_positive_parameters
