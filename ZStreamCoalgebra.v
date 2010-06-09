(************************************************************************)
(* Copyright 2008 Milad Niqui                                           *)
(* This file is distributed under the terms of the                      *)
(* GNU Lesser General Public License Version 3                          *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses/lgpl-3.0.html>         *)
(************************************************************************)

Require Coq.ZArith.BinInt.
Require Import WeaklyFinalCoalgebra.

(** Implementation of the weakly final coalgebra of streams of integers. *)

Let B:=ZArith.BinInt.Z.

Set Implicit Arguments.


(* Streams from the scratch *)
Section Streams.

Variable A : Type.

CoInductive Stream (A : Type) : Type :=  Cons : A -> Stream A -> Stream A.

Definition tl (A : Type) (x : Stream A) := match x with | Cons _ s => s end.
Definition hd (A : Type) (x : Stream A) := match x with | Cons a _ => a end.

Lemma unfold_Stream : forall x:Stream A, x = match x with | Cons a s => Cons a s end. 
Proof.
  intros [x xs]; reflexivity. 
Defined.

Lemma hd_tl_id:forall xs:Stream A, xs = Cons (hd xs) (tl xs).
Proof.
 intros [x xs]; trivial.
Defined.

End Streams.

Unset Implicit Arguments.

Ltac decomp_coind := intros; let LHS := match goal with
                                        | |-(?a = _) => constr: a
                                        | |-(_ ?a _) => constr: a
                                        end
                             in rewrite (unfold_Stream LHS); reflexivity.


Module Bisimulation_For_Coalgebra_Streams <: Bisimulation_For_Coalgebra.

Let B_pow_inf := Stream B.

Definition F_ (X:Set) := (B * X)%type.

Definition lift_F_ (X Y:Set) (f:X->Y) (bx: F_ X) : F_ Y := let (b0,x0):=bx in (b0,f x0).

Lemma lift_F_id :forall X (bx: F_ X), bx = lift_F_ X X (fun x0 : X => x0) bx.
Proof.
 intros X [b x]; trivial.
Defined.

Lemma lift_F_compose (X Y Z:Set) (g:X->Y) (f:Y->Z) bx: 
   (fun bx0 => lift_F_ Y Z f (lift_F_ X Y g bx0)) bx = lift_F_ X Z (fun x => f (g x)) bx.
Proof.
 destruct bx as [b0 x0]; trivial.
Defined.

Lemma lift_F_extensionality: forall (X Y:Set) (f0 f1:X->Y) bx, (forall x, f0 x = f1 x) -> lift_F_  _ _ f0 bx = lift_F_ _ _ f1 bx.
Proof.
 intros X Y f0 f1 bx hyp_ext;
 unfold lift_F_; destruct bx as [b x]; repeat rewrite hyp_ext; trivial.
Defined.

Record F_coalgebra : Type :=
{ states : Set 
; transition : states -> F_ states
}.

Definition hd_ (S1:F_coalgebra) : S1.(states) -> B :=
       match S1 with
       | Build_F_coalgebra S1_ tr => fun s => fst (tr s)
       end.

Definition tl_ (S1:F_coalgebra) : S1.(states) -> S1.(states) :=
       match S1 with
       | Build_F_coalgebra S1_ tr => fun s => snd (tr s)
       end.

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

CoInductive maximal_bisimulation_Str (S1 S2:F_coalgebra) (s1:S1.(states)) (s2:S2.(states)) : Prop :=
    max_bisim_str : hd_ S1 s1 = hd_ S2 s2 -> maximal_bisimulation_Str S1 S2 (tl_ _ s1) (tl_ _ s2) -> maximal_bisimulation_Str S1 S2 s1 s2.

Definition maximal_bisimulation:= maximal_bisimulation_Str.

Definition maximal_bisimulation_Str_tl : forall (S1 S2:F_coalgebra), 
{s1s2 : S1.(states) * S2.(states)| maximal_bisimulation _ _ (fst s1s2) (snd s1s2)} -> 
{s1s2 : S1.(states) * S2.(states)| maximal_bisimulation _ _ (fst s1s2) (snd s1s2)}.
Proof.
 intros [X_st X_tr] [Y_st Y_tr] [[x y] [_ hyp_tl]].
 exists (tl_  (Build_F_coalgebra X_st X_tr) x,tl_ (Build_F_coalgebra Y_st Y_tr) y).
 exact hyp_tl.
Defined.

Lemma maximal_bisimulation_is_bisimulation: forall (S1 S2:F_coalgebra), is_F_bisimulation _ _ (maximal_bisimulation S1 S2).
Proof.
 intros S1 S2.
 exists (fun s1s2h=> (hd_ _ (fst (projT1 s1s2h)), maximal_bisimulation_Str_tl S1 S2 s1s2h)). 
 generalize S1 S2.
 intros [X_st X_tr] [Y_st Y_tr] [[x y] [hyp_hd hyp_tl]].
 simpl; split; rewrite surjective_pairing; trivial. 
  simpl in hyp_hd; rewrite hyp_hd; trivial.
Defined.


Lemma maximal_bisimulation_is_maximal:forall (S1 S2:F_coalgebra), is_maximal_F_bisimulation _ _ (maximal_bisimulation S1 S2).
Proof.
 intros S1 S2.
 split.
  exists (maximal_bisimulation_is_bisimulation S1 S2); trivial.
  intros R' [hyp_R' _].
  revert S1 S2 R' hyp_R'.
  cofix.
  intros [X X_tr] [Y Y_tr] R' h_coind s1 s2 hyp'.
  constructor.
   destruct h_coind as [gamma hyp].
   set (s1s2h:=existS (fun s1s2=> R' (fst s1s2) (snd s1s2)) (s1,s2) hyp').
   destruct (hyp s1s2h) as [hyp1 hyp2].
   clear hyp.
   unfold F_ in gamma.
   unfold lift_F_ in hyp1,hyp2; simpl in hyp1, hyp2.
   unfold hd_.
   rewrite <- hyp1.
   rewrite <- hyp2.
   destruct (gamma s1s2h); trivial.

   apply (maximal_bisimulation_is_maximal _ _ R' h_coind).
   destruct h_coind as [gamma hyp].
   set (s1s2h:=existS (fun s1s2=> R' (fst s1s2) (snd s1s2)) (s1,s2) hyp').
   destruct (hyp s1s2h) as [hyp1 hyp2].
   clear hyp.
   unfold F_ in gamma.
   unfold lift_F_ in hyp1,hyp2; simpl in hyp1, hyp2.
   unfold tl_.
   set (gam_s1s2h:=gamma s1s2h).
   set (xyh:=snd (gam_s1s2h)).
   set (b0:=fst (gam_s1s2h)).
   assert (hyp1_1:(b0,fst (projT1 xyh))=X_tr s1);
    [rewrite <- hyp1; subst xyh gam_s1s2h; destruct (gamma s1s2h); trivial|].
   assert (hyp2_1:(b0,snd (projT1 xyh))=Y_tr s2);
    [rewrite <- hyp2; subst xyh gam_s1s2h; destruct (gamma s1s2h); trivial|].
   rewrite <- hyp1_1.
   rewrite <- hyp2_1.
   destruct xyh as [[x y] h].
   trivial.
Defined.

Definition weak_pullback (X Y Z:Set) (f:X->Z) (g:Y->Z):={ xy:(X*Y) | f(fst xy)=g(snd xy)}.

Definition wkpk_id_rht: forall (X Y Z:Set) (f:X->Z) (g:Y->Z), 
    weak_pullback _ _ _ (lift_F_ _ _ f) (lift_F_ _ _ g) -> F_ (weak_pullback _ _ _ f g).
Proof.
 intros X Y Z f g [[[b0 x] [b1 y]] h]. 
 simpl in h.
 refine (b0,_).
 exists (x,y).
 simpl.
 change (snd (b0, f x) = snd (b1, g y)).
 rewrite h; reflexivity.
Defined.

Definition wkpk_id_lft: forall (X Y Z:Set) (f:X->Z) (g:Y->Z), 
 F_ (weak_pullback _ _ _ f g) -> weak_pullback _ _ _ (lift_F_ _ _ f) (lift_F_ _ _ g).
Proof.
 intros X Y Z f g [b [[x y] h]].
 simpl in h.
 exists ((b,x),(b,y)).
 simpl.
 rewrite h; trivial.
Defined.

Lemma F_pres_weak_pullback_arr: forall (X Y Z:Set) (f:X->Z) (g:Y->Z) 
                                  (wxy:weak_pullback _ _ _ (lift_F_ _ _ f) (lift_F_ _ _ g)), 
 lift_F_ (weak_pullback _ _ _ f g) X (fun xy=>fst (projT1 xy)) (wkpk_id_rht _ _ _ _ _ wxy) =  fst (projT1 wxy) /\
 lift_F_ (weak_pullback _ _ _ f g) Y (fun xy=>snd (projT1 xy)) (wkpk_id_rht _ _ _ _ _ wxy) =  snd (projT1 wxy). 
Proof.
 intros X Y Z f g [[[b0 x] [b1 y]] h].
 simpl in h.
 unfold wkpk_id_rht.
 unfold lift_F_.
 simpl; split; trivial.
 f_equal.
 change (fst (b0, f x) = fst (b1, g y)).
 rewrite h; reflexivity.
Defined.

End Bisimulation_For_Coalgebra_Streams. 


Module Streams_as_Weakly_Final_Coalgebra  <: Weakly_Final_Coalgebra.

Include Bisimulation_For_Coalgebra_Streams.

Module Import Streams_Coalgebra := Bisimulation_theory Bisimulation_For_Coalgebra_Streams.

Definition is_weakly_final (w:F_coalgebra) := forall (S0:F_coalgebra),
   { F_unfold_ : S0.(states) -> w.(states) | 
     forall s0, w.(transition) (F_unfold_ s0) = lift_F_ _ _ F_unfold_ (S0.(transition) s0)}.


Definition Str := Build_F_coalgebra B_pow_inf (fun s => (hd s, tl s)).

Definition w:=Str.

CoFixpoint Str_unfold (S0:F_coalgebra) (s0: S0.(states)) : Str.(states):=
                                   Cons (hd_ S0 s0) (Str_unfold S0 (tl_ S0 s0)).

Lemma Str_unfold_unfolded:forall (S0:F_coalgebra) (s0: S0.(states)), Str_unfold S0 s0 = Cons (hd_ S0 s0) (Str_unfold S0 (tl_ S0 s0)).
Proof.
 decomp_coind.
Defined.

Lemma commutativity_Str_unfold  (S0: F_coalgebra) (x:S0.(states)) : 
       Str.(transition) (Str_unfold S0 x) = (lift_F_ _ _ (Str_unfold S0)) (S0.(transition) x).
Proof.
 destruct S0 as [s0 s0_tr].
 rewrite Str_unfold_unfolded; simpl.
 set (s0_tr_x:=s0_tr x). 
 destruct s0_tr_x as (b,tr); trivial.
Defined.

Lemma w_is_weakly_final:is_weakly_final w.
Proof.
 intros S0.
 exists (Str_unfold S0).
 apply commutativity_Str_unfold.
Defined.

Definition F_unfold (S0:F_coalgebra) := proj1_sig (w_is_weakly_final S0).
Definition commutativity_F_unfold (S0:F_coalgebra) :forall (x:S0.(states)), w.(transition) (F_unfold S0 x) = (lift_F_ _ _ (F_unfold S0)) (S0.(transition) x) := proj2_sig (w_is_weakly_final S0).
Definition bisimilar := maximal_bisimulation w w.

Notation " A (=) B " := (maximal_bisimulation w w A B) (at level 70).

Definition refl_bisimilar := refl_bisimilar w.

Definition sym_bisimilar := sym_bisimilar w.

Definition trans_bisimilar := trans_bisimilar w.

Lemma Str_unfold_bisim_unique:forall (S0:F_coalgebra) f, 
   (forall (s0: S0.(states)), (f s0) = Cons (hd_ S0 s0) (f (tl_ S0 s0))) -> forall s, 
        Str_unfold S0 s(=) f s.
Proof.
 cofix.
 intros S0 f H s0.
 rewrite Str_unfold_unfolded.
 rewrite (H s0).
 constructor; trivial.
 simpl.
 apply (Str_unfold_bisim_unique _ _ H (tl_ S0 s0)). 
Defined.


Lemma Str_unique_with_cons:forall (S0:F_coalgebra) f g, 
   (forall (s0: S0.(states)), (f s0) = Cons (hd_ S0 s0) (f (tl_ S0 s0))) -> 
   (forall (s0: S0.(states)), (g s0) = Cons (hd_ S0 s0) (g (tl_ S0 s0))) -> forall s, 
        f s(=) g s.
Proof.
 intros S0 f g Hf Hg s0.
 apply trans_bisimilar with (Str_unfold S0 s0); 
 [apply sym_bisimilar|]; apply Str_unfold_bisim_unique ; assumption.
Defined.


Lemma F_unique:forall (S0:F_coalgebra) f g, 
   (forall (s0: S0.(states)), w.(transition) (f s0) = (lift_F_ _ _ f) (S0.(transition) s0) ) ->
   (forall (s0: S0.(states)), w.(transition) (g s0) = (lift_F_ _ _ g) (S0.(transition) s0) ) ->
   forall s, f s(=) g s.
Proof.
 intros S0 f g; simpl; unfold lift_F_.
 intros Hf Hg.
 apply Str_unique_with_cons; intros s; assert (Hfs:=Hf s);assert (Hgs:=Hg s); destruct S0 as [S0_st S0_tr]; simpl in f,g,Hf,Hg,s, Hfs, Hgs.
   rewrite (hd_tl_id (f s)); apply f_equal2; 
   [ unfold hd_; change (fst (hd (f s), tl (f s))=fst (S0_tr s))
   | unfold tl_; change (snd (hd (f s), tl (f s))=f (snd (S0_tr s)))
   ]; destruct (S0_tr s) as [h_s t_s]; rewrite Hfs; simpl; trivial.
   rewrite (hd_tl_id (g s)); apply f_equal2; 
   [ unfold hd_; change (fst (hd (g s), tl (g s))=fst (S0_tr s))
   | unfold tl_; change (snd (hd (g s), tl (g s))=g (snd (S0_tr s)))
   ]; destruct (S0_tr s) as [h_s t_s]; rewrite Hgs; simpl; trivial.
Defined.   

Lemma lift_F_extensionality_bisim_Str: forall (X:Set) (f0 f1:X->Str.(states)) bx, (forall x, f0 x (=) f1 x) -> fst (lift_F_  _ _ f0 bx) = fst (lift_F_ _ _ f1 bx) /\ snd  (lift_F_  _ _ f0 bx) (=) snd (lift_F_ _ _ f1 bx).
Proof.
 intros X f0 f1 bx hyp_ext.
 unfold lift_F_.
 destruct bx as [b x]; split; simpl; trivial.
Defined.

Lemma rel_image_lift_F_Str_bisimilar_spelled: forall (b_x b_y: F_ Str.(states)),  
     rel_image_lift_F_ _ _ bisimilar b_x b_y <-> fst b_x = fst b_y /\ snd b_x (=) snd b_y.
Proof.
 intros [b_x [x xs]] [b_y [y ys]].
 simpl; unfold rel_image_lift_F_.
 split;
 simpl.
 (* ==> *)
 intros [x0 [y0 [[eq_1 eq_2] [eq_3 eq_4]]]].
  split.
  simpl in eq_1, eq_2.
  transitivity (hd x0);[|transitivity (hd y0); trivial; symmetry];
  match goal with 
  | [ id1 : (?X1, ?X3) = _  |- ?X1 =?X2 ] => match goal with 
                                             | [ id2: _ = (?X2, ?X4) |-  ?X1 =?X2 ] => change (fst(X1,X3)= fst(X2,X4));apply f_equal; trivial
                                             end
  end.
  apply trans_bisimilar with (tl x0);[|apply trans_bisimilar with (tl y0); trivial; apply sym_bisimilar];

  match goal with 
  | [ id1 : (?X3, ?X1) = _  |- ?X1 (=)?X2 ] => match goal with 
                                             | [ id2: _ = (?X4, ?X2) |-  ?X1 (=)?X2 ] => change (snd(X3,X1)(=) snd(X4,X2)); rewrite <- id2
                                             end
  end;
  apply refl_bisimilar.

 (* <== *)
 intros [hyp1 hyp2]. 
 simpl.
 exists (Cons b_x (Cons x xs)).
 exists (Cons b_y (Cons y ys)).
 split.
  constructor; assumption.
  split; simpl; trivial.
Defined.
 
Lemma lift_F_extensionality_bisim: forall (X:Set) (f0 f1:X->w.(states)) bx, (forall x, f0 x (=) f1 x) -> rel_image_lift_F_ _ _ bisimilar (lift_F_  _ _ f0 bx) (lift_F_ _ _ f1 bx).
Proof.
 intros X f0 f1 bx hyp_eq.
 apply <- rel_image_lift_F_Str_bisimilar_spelled.
 apply lift_F_extensionality_bisim_Str; assumption.
Defined.


End Streams_as_Weakly_Final_Coalgebra.
