import ActualAMSQuadrilateralVectors

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical

theorem actualTypeILeftHighest_calibrated (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h : ℕ) (hh : 1≤h) (l m c : ℕ) (hadm : m≤l+c) (s : QuantumCupIndex l m c) :
    actualTypeILeftHighest q hq hq1 h hh l m c s =
      canonicalizeActualTriple (ne_of_gt hq)
        (actualSymmetricCarrier q hq hq1 (h+1) l)
        (actualOppositeCarrier q hq hq1 (h+1) (by omega) m)
        (actualSymmetricCarrier q hq hq1 (h+1) c)
        (physicalTypeILeftCoupling q hq hq1 (h+1) (by omega) l m 0 c hadm (Or.inl rfl) s).val := by
  rcases s with ⟨⟨r,hr⟩,hl,hm⟩
  change r≤l at hl
  change m-r≤c at hm
  obtain ⟨p,hp⟩:=Nat.exists_eq_add_of_le hl
  have hl' : l=p+r := by omega
  clear hp
  subst l
  have hrm : r≤m := by omega
  obtain ⟨u,hu⟩:=Nat.exists_eq_add_of_le hrm
  have hm' : m=u+r := by omega
  clear hu
  subst m
  have huc : u≤c := by omega
  let A:=actualSymmetricCarrier q hq hq1 (h+1) (p+r)
  let B:=actualOppositeCarrier q hq hq1 (h+1) (by omega) (u+r)
  let C:=actualSymmetricCarrier q hq hq1 (h+1) c
  let D:=actualSymmetricCarrier q hq hq1 (h+1) ((p+r)+c-(u+r))
  let E:=actualMixedCarrier q hq hq1 (h+1) (by omega) ((p+r)-r) ((u+r)-r)
  let D':=actualSymmetricCarrier q hq hq1 (h+1) (p+c-u)
  let E':=actualMixedCarrier q hq hq1 (h+1) (by omega) p u
  have hD : D.irrep=D'.irrep := by
    apply Subtype.ext
    change mixedHighestDynkin (h+1) ((p+r)+c-(u+r)) 0=mixedHighestDynkin (h+1) (p+c-u) 0
    congr 1 <;> omega
  have hE : E.irrep=E'.irrep := by
    apply Subtype.ext
    change mixedHighestDynkin (h+1) ((p+r)-r) ((u+r)-r)=mixedHighestDynkin (h+1) p u
    rw [Nat.add_sub_cancel,Nat.add_sub_cancel]
  have hTree:=actualLeftVertexTree_highest_congr (amsActualVertexTable q hq hq1 (h+1) (by omega))
    A.irrep B.irrep C.irrep D.irrep E.irrep D'.irrep E'.irrep hD hE
  exact hTree.trans (actualAMSTable_TypeI_left_tree q hq hq1 h hh p u c huc r)

theorem actualTypeIRightHighest_calibrated (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h : ℕ) (hh : 1≤h) (l m c : ℕ) (hadm : m≤l+c) (t : QuantumCupIndex l m c) :
    actualTypeIRightHighest q hq hq1 h hh l m c t =
      canonicalizeActualTriple (ne_of_gt hq)
        (actualSymmetricCarrier q hq hq1 (h+1) l)
        (actualOppositeCarrier q hq hq1 (h+1) (by omega) m)
        (actualSymmetricCarrier q hq hq1 (h+1) c)
        (physicalTypeIRightCoupling q hq hq1 (h+1) (by omega) l m 0 c hadm (Or.inl rfl) t).val := by
  rcases t with ⟨⟨s,hs⟩,hl,hc⟩
  change s≤l at hl
  change m-s≤c at hc
  have hsm : s≤m := by omega
  obtain ⟨r,hr⟩:=Nat.exists_eq_add_of_le hsm
  have hm' : m=s+r := by omega
  subst m
  have hrc : r≤c := by omega
  obtain ⟨p,hp⟩:=Nat.exists_eq_add_of_le hrc
  have hc' : c=p+r := by omega
  clear hp
  subst c
  let A:=actualSymmetricCarrier q hq hq1 (h+1) l
  let B:=actualOppositeCarrier q hq hq1 (h+1) (by omega) (s+r)
  let C:=actualSymmetricCarrier q hq hq1 (h+1) (p+r)
  let D:=actualSymmetricCarrier q hq hq1 (h+1) (l+(p+r)-(s+r))
  let E:=actualMixedCarrier q hq hq1 (h+1) (by omega) ((p+r)-((s+r)-s)) s
  let E':=actualMixedCarrier q hq hq1 (h+1) (by omega) p s
  have hE : E.irrep=E'.irrep := by
    apply Subtype.ext
    change mixedHighestDynkin (h+1) ((p+r)-((s+r)-s)) s=mixedHighestDynkin (h+1) p s
    rw [Nat.add_sub_cancel_left,Nat.add_sub_cancel]
  have hTree:=actualRightVertexTree_highest_congr (amsActualVertexTable q hq hq1 (h+1) (by omega))
    A.irrep B.irrep C.irrep D.irrep E.irrep D.irrep E'.irrep rfl hE
  exact hTree.trans (actualAMSTable_TypeI_right_tree q hq hq1 h hh l p s
    (l+(p+r)-(s+r)) (by omega) hl r)

theorem actualTypeIILeftHighest_calibrated (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h : ℕ) (hh : 1≤h) (a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d) :
    actualTypeIILeftHighest q hq hq1 h hh a b c d r =
      (-1:ℝ)^(h*c) • canonicalizeActualTriple (ne_of_gt hq)
        (actualSymmetricCarrier q hq hq1 (h+1) a) (actualSymmetricCarrier q hq hq1 (h+1) b)
        (actualOppositeCarrier q hq hq1 (h+1) (by omega) c)
        (physicalTypeIICalibratedLeft q hq hq1 h a b c d hbal r).val :=
  actualAMSTable_TypeII_left_tree q hq hq1 h hh a b c d hbal r

theorem actualTypeIIRightHighest_calibrated (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h : ℕ) (hh : 1≤h) (a b c d : ℕ) (hbal : a+b=c+d) (t : QuantumCupIndex a c b) :
    actualTypeIIRightHighest q hq hq1 h hh a b c d t =
      (-1:ℝ)^(h*c) • canonicalizeActualTriple (ne_of_gt hq)
        (actualSymmetricCarrier q hq hq1 (h+1) a) (actualSymmetricCarrier q hq hq1 (h+1) b)
        (actualOppositeCarrier q hq hq1 (h+1) (by omega) c)
        (physicalTypeIICalibratedRight q hq hq1 h a b c d hbal t).val := by
  rcases t with ⟨⟨s,hs⟩,ha,hb⟩
  change s≤a at ha
  change c-s≤b at hb
  have hsc : s≤c := by omega
  obtain ⟨r,hr⟩:=Nat.exists_eq_add_of_le hsc
  have hc' : c=s+r := by omega
  subst c
  have hrb : r≤b := by omega
  obtain ⟨p,hp⟩:=Nat.exists_eq_add_of_le hrb
  have hb' : b=p+r := by omega
  clear hp
  subst b
  let A:=actualSymmetricCarrier q hq hq1 (h+1) a
  let B:=actualSymmetricCarrier q hq hq1 (h+1) (p+r)
  let C:=actualOppositeCarrier q hq hq1 (h+1) (by omega) (s+r)
  let D:=actualSymmetricCarrier q hq hq1 (h+1) d
  let E:=actualMixedCarrier q hq hq1 (h+1) (by omega) ((p+r)-((s+r)-s)) s
  let E':=actualMixedCarrier q hq hq1 (h+1) (by omega) p s
  have hE : E.irrep=E'.irrep := by
    apply Subtype.ext
    change mixedHighestDynkin (h+1) ((p+r)-((s+r)-s)) s=mixedHighestDynkin (h+1) p s
    rw [Nat.add_sub_cancel_left,Nat.add_sub_cancel]
  have hTree:=actualRightVertexTree_highest_congr (amsActualVertexTable q hq hq1 (h+1) (by omega))
    A.irrep B.irrep C.irrep D.irrep E.irrep D.irrep E'.irrep rfl hE
  exact hTree.trans (actualAMSTable_TypeII_right_tree q hq hq1 h hh a p s d (by omega) ha r)

end AMSPhysical
#print axioms AMSPhysical.actualTypeILeftHighest_calibrated
#print axioms AMSPhysical.actualTypeIRightHighest_calibrated
#print axioms AMSPhysical.actualTypeIILeftHighest_calibrated
#print axioms AMSPhysical.actualTypeIIRightHighest_calibrated
