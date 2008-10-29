(************************************************************************)
(* Copyright 2008 Milad Niqui                                           *)
(* This file is distributed under the terms of the                      *)
(* GNU Lesser General Public License Version 3                          *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses/lgpl.txt>              *)
(************************************************************************)

Require Export ExtensionalFunctor.

(** Module types and theories for:
    
   * Coalgebras of (extensional) functors;
   * Bisimulation relation on the coalgebras.
*)

Module Type Set_Coalgebra.

Include Type Set_Functor.

Record F_coalgebra : Type :=
{ states : Set 
; transition : states -> F_ states
}.

End Set_Coalgebra.

Module Set_Coalgebra_theory (MF:Set_Coalgebra).

Import MF.


Lemma F_coalgebra_compose:forall (S0 S1 S2:F_coalgebra) f  g,
   (forall (s0: S0.(states)), S1.(transition) (f s0) = lift_F_ _ _ f (S0.(transition) s0))  -> 
   (forall (s1: S1.(states)), S2.(transition) (g s1) = lift_F_ _ _ g (S1.(transition) s1))  -> 
        forall s0, S2.(transition) (g (f s0)) = lift_F_ _ _ (fun s=>g (f s)) (S0.(transition) s0).
Proof.
 intros [X0 X0_tr] [X1 X1_tr] [X2 X2_tr]; simpl; intros f g Hf Hg s0.
  rewrite (Hg (f s0)). 
  rewrite (Hf s0).
  rewrite lift_F_compose; trivial.
Defined.

End Set_Coalgebra_theory.


Module Type Bisimulation_For_Coalgebra.

Include Type Set_Coalgebra.

Definition rel_image_lift_F_ (S1 S2:F_coalgebra) (R:S1.(states) -> S2.(states) -> Prop) 
         (b_x : F_ (states S1)) (b_y : F_ (states S2)) : Prop :=
       exists x : states S1,
         exists y : states S2,
           R x y /\ b_x = transition S1 x /\ b_y = transition S2 y.

Definition is_F_bisimulation (S1 S2:F_coalgebra) (R:S1.(states) -> S2.(states) -> Prop) :=
 { gamma : {s1s2 : states S1 * states S2 | R (fst s1s2) (snd s1s2)} -> 
            F_ {s1s2 : states S1 * states S2 | R (fst s1s2) (snd s1s2)} | 
    forall  (s1s2_h:{s1s2 : states S1 * states S2 | R (fst s1s2) (snd s1s2)}), 
            lift_F_ _ _ (fun z=>fst(proj1_sig z)) (gamma s1s2_h)=S1.(transition) (fst(proj1_sig s1s2_h)) /\
            lift_F_ _ _ (fun z=>snd(proj1_sig z)) (gamma s1s2_h)=S2.(transition) (snd(proj1_sig s1s2_h))}.

Definition is_F_bisimulation_strong (S1 S2:F_coalgebra) (R:S1.(states) -> S2.(states) -> Set) :=
 { gamma : {s1s2 : states S1 * states S2 & R (fst s1s2) (snd s1s2)} -> 
            F_ {s1s2 : states S1 * states S2 & R (fst s1s2) (snd s1s2)} & 
    forall  (s1s2_h:{s1s2 : states S1 * states S2 & R (fst s1s2) (snd s1s2)}), 
            lift_F_ _ _ (fun z=>fst(projT1 z)) (gamma s1s2_h)=S1.(transition) (fst(projT1 s1s2_h)) /\
            lift_F_ _ _ (fun z=>snd(projT1 z)) (gamma s1s2_h)=S2.(transition) (snd(projT1 s1s2_h))}.


Definition is_maximal_F_bisimulation (S1 S2:F_coalgebra) (R:S1.(states) -> S2.(states) -> Prop) :=
  (exists a:is_F_bisimulation S1 S2 R, True) /\ forall R', (exists a:is_F_bisimulation_strong S1 S2 R',True) -> forall s1 s2, R' s1 s2 -> R s1 s2.

Parameter maximal_bisimulation: forall (S1 S2:F_coalgebra), S1.(states) -> S2.(states) -> Prop.

Axiom maximal_bisimulation_is_bisimulation: forall (S1 S2:F_coalgebra), is_F_bisimulation _ _ (maximal_bisimulation S1 S2).

Axiom maximal_bisimulation_is_maximal:forall (S1 S2:F_coalgebra), is_maximal_F_bisimulation _ _ (maximal_bisimulation S1 S2).

Definition weak_pullback (X Y Z:Set) (f:X->Z) (g:Y->Z):={ xy:(X*Y) | f(fst xy)=g(snd xy)}.

Parameter wkpk_id_rht: forall (X Y Z:Set) (f:X->Z) (g:Y->Z), 
 weak_pullback _ _ _ (lift_F_ _ _ f) (lift_F_ _ _ g) -> F_ (weak_pullback _ _ _ f g).

Axiom F_pres_weak_pullback_arr: forall (X Y Z:Set) (f:X->Z) (g:Y->Z) 
                                  (wxy:weak_pullback _ _ _ (lift_F_ _ _ f) (lift_F_ _ _ g)), 
 lift_F_ (weak_pullback _ _ _ f g) X (fun xy=>fst (projT1 xy)) (wkpk_id_rht _ _ _ _ _ wxy) =  fst (projT1 wxy) /\
 lift_F_ (weak_pullback _ _ _ f g) Y (fun xy=>snd (projT1 xy)) (wkpk_id_rht _ _ _ _ _ wxy) =  snd (projT1 wxy). 

End Bisimulation_For_Coalgebra.

Module Bisimulation_theory (MB:Bisimulation_For_Coalgebra).

Import MB.
Export MB.

Include (Set_Coalgebra_theory MB).

Definition lift_B_id:=MB.lift_F_id.
Definition lift_B_extensionality:=MB.lift_F_extensionality.
Definition relation_lift_B_:=MB.rel_image_lift_F_.


Lemma is_F_bisimulation_is_F_bisimulation_strong (S1 S2:F_coalgebra) (R:S1.(states)->S2.(states)->Prop): is_F_bisimulation _ _ R -> is_F_bisimulation_strong _ _ R.
Proof.
 intros S1 S2 R  [gamma hyp].
 set (RS12:={s1s2 : states S1 * states S2 | R (fst s1s2) (snd s1s2)}).
 set (RS12_:={s1s2 : states S1 * states S2 & R (fst s1s2) (snd s1s2)}).
 set (id_:=fun s1s2h:RS12=> existS (fun z=>R (fst z) (snd z)) (fst (projT1 s1s2h),snd (projT1 s1s2h)) (projT2 s1s2h):RS12_).
 set (id__:=fun s1s2h:RS12_=> exist (fun z=>R (fst z) (snd z)) (fst (projT1 s1s2h),snd (projT1 s1s2h)) (projT2 s1s2h):RS12).
 exists (fun s2s1h => lift_F_ _ _ id_ (gamma (id__ s2s1h)):F_ RS12_).
 intros s1s2_h.
 destruct (hyp s1s2_h) as [hyp1 hyp2].
 destruct s1s2_h as [[s1 s2] hypR].
 split; simpl; simpl in hyp1, hyp2;
 [rewrite <- hyp1 |rewrite <- hyp2];
  rewrite lift_F_compose;
  apply lift_F_extensionality;
  intros [[x1 x2] hx]; trivial.
Defined.

Lemma is_F_bisimulation_strong_Prop_is_F_bisimulation (S1 S2:F_coalgebra) (R:S1.(states)->S2.(states)->Prop): is_F_bisimulation_strong _ _ R -> is_F_bisimulation _ _ R.
Proof.
 intros S1 S2 R  [gamma hyp].
 set (RS12:={s1s2 : states S1 * states S2 | R (fst s1s2) (snd s1s2)}).
 set (RS12_:={s1s2 : states S1 * states S2 & R (fst s1s2) (snd s1s2)}).
 set (id_:=fun s1s2h:RS12=> existS (fun z=>R (fst z) (snd z)) (fst (projT1 s1s2h),snd (projT1 s1s2h)) (projT2 s1s2h):RS12_).
 set (id__:=fun s1s2h:RS12_=> exist (fun z=>R (fst z) (snd z)) (fst (projT1 s1s2h),snd (projT1 s1s2h)) (projT2 s1s2h):RS12).
 exists (fun s2s1h => lift_F_ _ _ id__ (gamma (id_ s2s1h)):F_ RS12).
 intros s1s2_h.
 destruct (hyp s1s2_h) as [hyp1 hyp2].
 destruct s1s2_h as [[s1 s2] hypR].
 split; simpl; simpl in hyp1, hyp2;
 [rewrite <- hyp1 |rewrite <- hyp2];
  rewrite lift_F_compose;
  apply lift_F_extensionality;
  intros [[x1 x2] hx]; trivial.
Defined.

Lemma delta_is_F_bisimulation (S1:F_coalgebra) :is_F_bisimulation _ _ (@eq S1.(states)).
Proof.
 intros S1.
 unfold is_F_bisimulation.
 exists (fun s1s2_h=>lift_F_ _ _ (fun (s:S1.(states))=>exist (fun z => (fst z = snd z)) (s,s) (refl_equal s)) (S1.(transition) (fst (proj1_sig s1s2_h)))).
 intros [[s1 s2] hyp]; split; simpl; simpl in hyp;
 rewrite lift_F_compose; rewrite lift_F_id; [| rewrite hyp]; trivial.
Defined.


Lemma inv_is_F_bisimulation (S1 S2:F_coalgebra) (R:S1.(states)->S2.(states)->Prop): is_F_bisimulation _ _ R -> is_F_bisimulation _ _ (fun x=>(fun y=>R y x)).
Proof.
 intros S1 S2 R  [gamma gamma_prop].
 set (RS21:={s2s1 : states S2 * states S1 | R (snd s2s1) (fst s2s1)}).
 set (RS12:={s1s2 : states S1 * states S2 | R (fst s1s2) (snd s1s2)}).
 set (i:=fun s1s2h:RS12=>(exist (fun z=>R (snd z) (fst z)) (snd (proj1_sig s1s2h),fst (proj1_sig s1s2h)) (proj2_sig s1s2h))).
 set (i_inv:=fun s2s1h:RS21=>(exist (fun z=>R (fst z) (snd z)) (snd (proj1_sig s2s1h),fst (proj1_sig s2s1h)) (proj2_sig s2s1h))).
 exists (fun s2s1h => lift_F_ _ _ i (gamma (i_inv s2s1h)):F_ RS21).
 intros s1s2h.
 generalize (gamma_prop (i_inv s1s2h)).
 destruct s1s2h as  [[s1 s2] hyp].
 simpl in hyp.
 simpl; intros [g_p1 g_p2]; split; simpl; rewrite lift_F_compose;
 [ rewrite <- g_p2
 | rewrite <- g_p1
 ]; trivial.
Defined.

Definition relation_carrier S1 S2 (R:S1.(states)->S2.(states)->Prop):=
       {s1s2 : states S1 * states S2 | R (fst s1s2) (snd s1s2)} .

Definition compose_relation S1 S2 S3 (R12:S1.(states)->S2.(states)->Prop) 
                                     (R23:S2.(states)->S3.(states)->Prop) x z:Prop :=
                                         exists y, R12 x y/\ R23 y z.

Definition compose_carrier_strong (S1 S2 S3:F_coalgebra) R12 R23:=
       {s1s3 : S1.(states) * S3.(states) & {s2:S2.(states)  | R12 (fst s1s3) s2 /\ R23 s2 (snd s1s3)}}.

Definition weak_pullback_Rel (S1 S2 S3:F_coalgebra) R12 R23 :=
           let RS12:={s1s2 : states S1 * states S2 | R12 (fst s1s2) (snd s1s2)} in 
           let RS23:={s2s3 : states S2 * states S3 | R23 (fst s2s3) (snd s2s3)} in
           let r2:=fun r:RS12 => (snd (proj1_sig r)) in
           let r3:=fun r:RS23 => (fst (proj1_sig r)) in
            weak_pullback _ _ _ r2 r3.

Let i_comp_pullback (S1 S2 S3:F_coalgebra) R12 R23 :
    {s1s3 : S1.(states) * S3.(states) & {s2:S2.(states)  | R12 (fst s1s3) s2 /\ R23 s2 (snd s1s3)}}->
                               weak_pullback_Rel _ _ _ R12 R23.
Proof.
 intros S1 S2 S3 R12 R23 [[s1 s3] [s2 [hyp12 hyp23]]];  unfold weak_pullback_Rel.
 set (RS12:={s1s2 : states S1 * states S2 | R12 (fst s1s2) (snd s1s2)}).
 set (RS23:={s2s3 : states S2 * states S3 | R23 (fst s2s3) (snd s2s3)}).
 set (r2:=fun r:RS12 => (snd (proj1_sig r))).
 set (r3:=fun r:RS23 => (fst (proj1_sig r))).
 set (s1s2h:=exist (fun xy=>(R12 (fst xy) (snd xy))) (s1,s2) hyp12:RS12).
 set (s2s3h:=exist (fun xy=>(R23 (fst xy) (snd xy))) (s2,s3) hyp23:RS23).
 exact (exist (fun xy : RS12 * RS23 => r2 (fst xy) = r3 (snd xy)) (s1s2h, s2s3h) (refl_equal s2)).
Defined.

Let j_comp_pullback (S1 S2 S3:F_coalgebra) R12 R23 : weak_pullback_Rel _ _ _ R12 R23->
      {s1s3 : S1.(states) * S3.(states) & {s2:S2.(states)  | R12 (fst s1s3) s2 /\ R23 s2 (snd s1s3)}}. 
Proof.
 intros S1 S2 S3 R12 R23 [[[[s1 s2] hyp12] [[s2' s3] hyp23]] hyp].
 simpl in  hyp, hyp23, hyp12.
 exists (s1,s3); exists s2; simpl; subst s2'; split; assumption.
Defined.

Lemma sigT_rewrite_1:forall (X Y Z:Set) (P:Y->Prop) (h1:Y=Z), {f:X->Y | forall x, P (f x)} -> 
 let id_rht:=(fun z:Z => eq_rec Y (fun Z0 : Set => Z0 -> Y) (fun y0 : Y => y0) Z h1 z) in 
   {g:X->Z | forall x, P (id_rht (g x))}.
Proof.
 intros X Y Z P h1 [f hyp_f] id_rht.
 set (id_lft:=(fun y:Y=>(eq_rec Y (fun Z0 : Set => Z0) y Z h1)):Y->Z).
 exists (fun x=> id_lft (f x)).
 intros x.
 generalize (hyp_f x).
 unfold id_lft, id_rht.
 intros hyp.
 vm_compute.
 case h1.
 trivial.
Defined.

Lemma sigT_rewrite_2:forall (X Y Z:Set) (P:(X->Z->Prop)) (h1:Y=Z), 
 let id_lft:=(fun y:Y=>(eq_rec Y (fun Z0 : Set => Z0) y Z h1)) in 
   {f:X->Y | forall x, P x (id_lft (f x))} ->  {g:X->Z | forall x, P x (g x)}.
Proof.
 intros X Y Z P h1 id_lft [f hyp_f].
 set (id_rht:=(fun z:Z => eq_rec Y (fun Z0 : Set => Z0 -> Y) (fun y0 : Y => y0) Z h1 z):Z->Y).
 exists (fun x=> id_lft (f x)).
 assumption.
Defined.


Definition pre_bisim_pulback_structure (S1 S2 S3:F_coalgebra) R12 R23: 
                             is_F_bisimulation _ _ R12 -> is_F_bisimulation _ _ R23 ->
                     weak_pullback_Rel S1 S2 S3 R12 R23 -> 
           let RS12:={s1s2 : states S1 * states S2 | R12 (fst s1s2) (snd s1s2)} in 
           let RS23:={s2s3 : states S2 * states S3 | R23 (fst s2s3) (snd s2s3)} in
           let r2:=fun r:RS12 => (snd (proj1_sig r)) in
           let r3:=fun r:RS23 => (fst (proj1_sig r)) in
            weak_pullback _ _ _  (lift_F_ _ _ r2) (lift_F_ _ _ r3).
Proof.
 intros S1 S2 S3 R12 R23 [gamma1 hyp1] [gamma2 hyp2] [[a12 a23] hyp] RS12 RS23 r2 r3.
 exists (gamma1 a12, gamma2 a23).
 simpl.
 destruct (hyp1 a12) as [_ hyp12].
 destruct (hyp2 a23) as [hyp21 _].
 unfold r2, r3, RS12, RS23; rewrite hyp12; rewrite hyp21.
 simpl in hyp; rewrite hyp.
 reflexivity.
Defined.


Lemma pre_bisim_pulback_structure_prop1 (S1 S2 S3:F_coalgebra) R12 R23
    (hyp1:is_F_bisimulation _ _ R12) (hyp2:is_F_bisimulation _ _ R23) (x:weak_pullback_Rel S1 S2 S3 R12 R23):
     projT1 hyp1 (fst (projT1 x)) = fst (projT1 (pre_bisim_pulback_structure _ _ _ _ _ hyp1 hyp2 x)).
Proof.
 intros S1 S2 S3 R12 R23 [gamma1 hyp1] [gamma2 hyp2] [[ [[s1 s2] hyp12] [[s2' s3] hyp23]] hyp];
 trivial.
Defined.

Lemma pre_bisim_pulback_structure_prop2 (S1 S2 S3:F_coalgebra) R12 R23
    (hyp1:is_F_bisimulation _ _ R12) (hyp2:is_F_bisimulation _ _ R23) (x:weak_pullback_Rel S1 S2 S3 R12 R23):
     projT1 hyp2 (snd (projT1 x)) = snd (projT1 (pre_bisim_pulback_structure _ _ _ _ _ hyp1 hyp2 x)).
Proof.
 intros S1 S2 S3 R12 R23 [gamma1 hyp1] [gamma2 hyp2] [[ [[s1 s2] hyp12] [[s2' s3] hyp23]] hyp];
 trivial.
Defined.


Definition bisim_pulback_structure (S1 S2 S3:F_coalgebra) R12 R23
         (hyp1 : is_F_bisimulation S1 S2 R12)
         (hyp2 : is_F_bisimulation S2 S3 R23)
         (x : weak_pullback_Rel S1 S2 S3 R12 R23) :=
       wkpk_id_rht _ _ _ _ _
         (let RS12 := {s1s2 : states S1 * states S2 | R12 (fst s1s2) (snd s1s2)} in
          let RS23 := {s2s3 : states S2 * states S3 | R23 (fst s2s3) (snd s2s3)} in
          let r2 := fun r : RS12 => snd (proj1_sig r) in
          let r3 := fun r : RS23 => fst (proj1_sig r) in
          pre_bisim_pulback_structure S1 S2 S3 R12 R23 hyp1 hyp2 x).

Definition bisim_pulback_structure_prop1 (S1 S2 S3:F_coalgebra) R12 R23
    (hyp1:is_F_bisimulation _ _ R12) (hyp2:is_F_bisimulation _ _ R23) (x:weak_pullback_Rel S1 S2 S3 R12 R23):
     projT1 hyp1 (fst (projT1 x)) = 
     lift_F_ _ _ (fun x0:weak_pullback_Rel S1 S2 S3 R12 R23=>(fst (projT1 x0))) (bisim_pulback_structure _ _ _ _ _ hyp1 hyp2 x).
Proof.
 intros S1 S2 S3 R12 R23 hyp1 hyp2 x.
 set (RS12:={s1s2 : states S1 * states S2 | R12 (fst s1s2) (snd s1s2)}).
 set (RS23:={s2s3 : states S2 * states S3 | R23 (fst s2s3) (snd s2s3)}).
 set (r2:=fun r:RS12 => (snd (proj1_sig r))).
 set (r3:=fun r:RS23 => (fst (proj1_sig r))).
 unfold bisim_pulback_structure.
 destruct (F_pres_weak_pullback_arr RS12 RS23 S2.(states) r2 r3 (pre_bisim_pulback_structure S1 S2 S3 R12 R23 hyp1 hyp2 x)) as [rwt_tmp _].
 stepr (fst (projT1 (pre_bisim_pulback_structure S1 S2 S3 R12 R23 hyp1 hyp2 x))).
 rewrite <- (pre_bisim_pulback_structure_prop1 S1 S2 S3 R12 R23 hyp1 hyp2 x); reflexivity.
 symmetry; assumption.
Defined.

Definition bisim_pulback_structure_prop2 (S1 S2 S3:F_coalgebra) R12 R23
    (hyp1:is_F_bisimulation _ _ R12) (hyp2:is_F_bisimulation _ _ R23) (x:weak_pullback_Rel S1 S2 S3 R12 R23):
     projT1 hyp2 (snd (projT1 x)) = 
     lift_F_ _ _ (fun x0:weak_pullback_Rel S1 S2 S3 R12 R23=>(snd (projT1 x0))) (bisim_pulback_structure _ _ _ _ _ hyp1 hyp2 x).
Proof.
 intros S1 S2 S3 R12 R23 hyp1 hyp2 x.
 set (RS12:={s1s2 : states S1 * states S2 | R12 (fst s1s2) (snd s1s2)}).
 set (RS23:={s2s3 : states S2 * states S3 | R23 (fst s2s3) (snd s2s3)}).
 set (r2:=fun r:RS12 => (snd (proj1_sig r))).
 set (r3:=fun r:RS23 => (fst (proj1_sig r))).
 unfold bisim_pulback_structure.
 destruct (F_pres_weak_pullback_arr RS12 RS23 S2.(states) r2 r3 (pre_bisim_pulback_structure S1 S2 S3 R12 R23 hyp1 hyp2 x)) as [_ rwt_tmp].
 stepr (snd (projT1 (pre_bisim_pulback_structure S1 S2 S3 R12 R23 hyp1 hyp2 x))).
 rewrite <- (pre_bisim_pulback_structure_prop2 S1 S2 S3 R12 R23 hyp1 hyp2 x); reflexivity.
 symmetry; assumption.
Defined.

Lemma comp_is_F_bisimulation_str (S1 S2 S3:F_coalgebra) (R12:S1.(states)->S2.(states)->Prop) 
                                                        (R23:S2.(states)->S3.(states)->Prop): 
  is_F_bisimulation _ _ R12 -> is_F_bisimulation _ _ R23 -> 
       is_F_bisimulation_strong _ _ (fun x=>(fun z=>{y |  R12 x y/\ R23 y z})).
Proof.
 intros S1 S2 S3 R12 R23 [gamma1 hyp1] [gamma2 hyp2].
 set (RS12:={s1s2 : states S1 * states S2 | R12 (fst s1s2) (snd s1s2)}).
 set (RS23:={s2s3 : states S2 * states S3 | R23 (fst s2s3) (snd s2s3)}).
 set (r2:=fun r:RS12 => (snd (proj1_sig r))).
 set (r3:=fun r:RS23 => (fst (proj1_sig r))).
 set (R12_is_bisim:=exist
         (fun gamma=> forall s1s2_h ,
           lift_F_ _ _ (fun z =>fst(proj1_sig z))(gamma s1s2_h) = S1.(transition) (fst (proj1_sig s1s2_h)) /\
           lift_F_ _ _ (fun z =>snd(proj1_sig z))(gamma s1s2_h) =
                                                     S2.(transition) (snd (proj1_sig s1s2_h))) gamma1 hyp1).
 set (R23_is_bisim:=exist
         (fun gamma=> forall s2s3_h ,
           lift_F_ _ _ (fun z =>fst(proj1_sig z))(gamma s2s3_h) = S2.(transition) (fst (proj1_sig s2s3_h)) /\
           lift_F_ _ _ (fun z =>snd(proj1_sig z))(gamma s2s3_h) =
                                                     S3.(transition) (snd (proj1_sig s2s3_h))) gamma2 hyp2).
 set (X:=weak_pullback _ _ _ r2 r3).
 set (R12_o_R23:={s1s3 : S1.(states) * S3.(states) & {s2  | R12 (fst s1s3) s2 /\ R23 s2 (snd s1s3)}}).
 set (i:=fun s1s3h:R12_o_R23 => i_comp_pullback S1 S2 S3 R12 R23 s1s3h).
 set (j:=fun xyyz:X => j_comp_pullback S1 S2 S3 R12 R23 xyyz).
 set (alpha_X:=fun xyyz:X => bisim_pulback_structure _ _ _ _ _ R12_is_bisim R23_is_bisim xyyz).
 set (Fj__alpha_X__i:=fun s1s3h:R12_o_R23 => lift_F_ _ _ j (alpha_X (i s1s3h))).
 exists Fj__alpha_X__i.
 intros s1s3_h.
 split.

  set (r1:=fun r:RS12 => (fst (proj1_sig r))).
  assert (triangle1:forall z,fst (projT1 z) = r1 (fst (projT1 (i z)))).
   clear; intros [[s1 s3] [s2 [hyp1 hyp2]]]; trivial.
  rewrite triangle1.  
  assert (square2:forall x, 
       lift_F_ (weak_pullback_Rel S1 S2 S3 R12 R23) _ (fun x0=>r1 (fst (projT1 x0))) (alpha_X x) =
       S1.(transition) (r1 (fst (projT1 x)))) .
   clear.
   intros x.
   rewrite <- lift_F_compose with (Y:=RS12).
   destruct (hyp1 (fst (projT1 x))) as [hyp121 _].
   unfold r1 at 2; rewrite <- hyp121.
   assert (alpha_X_coalg:forall x,  lift_F_ (weak_pullback_Rel S1 S2 S3 R12 R23) _ 
                                     (fun x0=> fst (projT1 x0)) (alpha_X x) = gamma1 (fst (projT1 x)));
    [ clear; intros x; unfold alpha_X; rewrite <- bisim_pulback_structure_prop1; reflexivity|].
   rewrite alpha_X_coalg; reflexivity.
  rewrite <- square2. 
  unfold Fj__alpha_X__i.
  rewrite lift_F_compose.
  apply lift_F_extensionality.
  intros [[ [[s1 s2] hyp12] [[s2' s3] hyp23]] hyp]; reflexivity...

  set (r4:=fun r:RS23 => (snd (proj1_sig r))).
  assert (triangle1':forall z,snd (projT1 z) = r4 (snd (projT1 (i z)))).
   clear; intros [[s1 s3] [s2 [hyp1 hyp2]]]; trivial.
  rewrite triangle1'.  
  assert (square2':forall x, 
       lift_F_ (weak_pullback_Rel S1 S2 S3 R12 R23) _ (fun x0=>r4 (snd (projT1 x0))) (alpha_X x) =
       S3.(transition) (r4 (snd (projT1 x)))) .
   clear.
   intros x.
   rewrite <- lift_F_compose with (Y:=RS23).
   destruct (hyp2 (snd (projT1 x))) as [_ hyp232].
   unfold r4 at 2; rewrite <- hyp232.
   assert (alpha_X_coalg':forall x,  lift_F_ (weak_pullback_Rel S1 S2 S3 R12 R23) _ 
                                     (fun x0=> snd (projT1 x0)) (alpha_X x) = gamma2 (snd (projT1 x)));
    [ clear; intros x; unfold alpha_X; rewrite <- bisim_pulback_structure_prop2; reflexivity|].
   rewrite alpha_X_coalg'; reflexivity.
  rewrite <- square2'. 
  unfold Fj__alpha_X__i.
  rewrite lift_F_compose.
  apply lift_F_extensionality.
  intros [[ [[s1 s2] hyp12] [[s2' s3] hyp23]] hyp]; reflexivity.
Defined.

Theorem refl_bisimilar : forall S0 s, maximal_bisimulation S0 S0 s s.
Proof.
 intros S0 s.
 generalize (maximal_bisimulation_is_maximal S0 S0). 
 unfold is_maximal_F_bisimulation.
 intros [hyp1 hyp2].
 apply (hyp2 (@eq S0.(states))); trivial. 
 assert (a:=delta_is_F_bisimulation S0).
 exists (is_F_bisimulation_is_F_bisimulation_strong _ _ (@eq S0.(states)) a); trivial.
Defined.

Theorem sym_bisimilar : forall S0 s1 s2, maximal_bisimulation S0 S0 s1 s2 -> maximal_bisimulation S0 S0 s2 s1.
Proof.
 intros S0 s1 s2 hyp.
 generalize (maximal_bisimulation_is_maximal S0 S0).
 unfold is_maximal_F_bisimulation.
 intros [[hyp1 _] hyp2].
 apply (hyp2 (fun x =>(fun y=>maximal_bisimulation S0 S0 y x))); trivial.
 assert (a:=inv_is_F_bisimulation S0 S0 (maximal_bisimulation S0 S0) hyp1).
 exists (is_F_bisimulation_is_F_bisimulation_strong _ _ _  a); trivial.
Defined.

Theorem trans_bisimilar : forall S0 s1 s2 s3, maximal_bisimulation S0 S0 s1 s2 ->
                               maximal_bisimulation S0 S0 s2  s3 -> maximal_bisimulation S0 S0 s1 s3.
Proof.
 intros S0 s1 s2 s3 hyp12 hyp23.
 generalize (maximal_bisimulation_is_maximal S0 S0).
 unfold is_maximal_F_bisimulation.
 intros [[hyp1 _] hyp2].
 apply (hyp2 (fun x =>(fun z=>{ y | maximal_bisimulation S0 S0 x y/\maximal_bisimulation S0 S0 y z}))).
 assert (a:=comp_is_F_bisimulation_str S0 S0 S0 (maximal_bisimulation S0 S0) (maximal_bisimulation S0 S0) hyp1 hyp1).
 exists a; trivial.
 exists s2; split; trivial.
Defined.

End Bisimulation_theory.