(************************************************************************)
(* Copyright 2008 Milad Niqui                                           *)
(* This file is distributed under the terms of the                      *)
(* GNU Lesser General Public License Version 3                          *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses/lgpl.txt>              *)
(************************************************************************)

Require Import WeaklyFinalCoalgebra.

(** Implementation of the weakly final coalgebra of potentially
infinite natural numbers. *)


Section sum_addenda.

Lemma inl_injection:forall (A B:Type) (x y:A), inl B x = inl B y -> x=y.
Proof.
 intros A B x y hyp; injection hyp; trivial.
Defined.

Lemma inr_injection:forall (A B:Type) (x y:A), inr B x = inr B y -> x=y.
Proof.
 intros A B x y hyp; injection hyp; trivial.
Defined.

End sum_addenda.


(** Potentially infinite natural numbers *)
Section CoPeano.

CoInductive conat: Set :=  
| co_O : conat 
| co_S : conat -> conat.

Definition co_O_S (nstar:unit + conat) : conat  :=
    match nstar with
    | inl star => co_O
    | inr n => co_S n
    end.


Definition pred (n : conat) := 
    match n with
    | co_O => inl _ tt
    | co_S n' => inr _ n'
    end.

Lemma unfold_conat : forall n:conat, 
    n = match n with
        | co_O => co_O
        | co_S n' => co_S n'
        end.
Proof.
 intros [|n']; trivial.
Defined.

Lemma pred_id:forall n:conat, 
    n = co_O_S (pred n).
Proof.
 intros [|n']; trivial.
Defined.

Lemma pred_inl_co_O:forall (n:conat) (u:unit), inl conat u = pred n -> n = co_O.
Proof.
 intros [|n''] u hyp; trivial; discriminate hyp. 
Defined.

Lemma pred_inr_co_S:forall (n n':conat), inr unit n' = pred n -> n = co_S n'.
Proof.
 intros [|n''] n' hyp;
 [ discriminate hyp
 | rewrite (inr_injection _ _ _ _ hyp); trivial].
Defined.


(** This is useful for computing with [conat] inside Coq. 

[take_conat bound n] prints the natural number representation of
[n:conat] if it is smaller than the [bound]. *)

Fixpoint take_conat (bound:nat) (n:conat) {struct bound}: unit + nat :=
  match bound, n  with
  | O, co_O => inr unit O
  | O, co_S n' => inl nat tt
  | S b', co_O  => inr unit O
  | S b', co_S n' => match take_conat b' n' with
                         | inl u => inl nat u
                         | inr n'' => inr unit (S n'')
                         end
  end.


End CoPeano.


Module Bisimulation_For_Coalgebra_CoPeano <: Bisimulation_For_Coalgebra.

Definition F_ (X:Set) := (unit + X)%type.

Definition lift_F_ (X Y:Set) (f:X->Y) (bx: F_ X) : F_ Y:=
       match bx with
       | inl star => inl Y star
       | inr x => inr unit (f x)
       end.

Lemma lift_F_id :forall X (bx: F_ X), bx = lift_F_ X X (fun x0 : X => x0) bx.
Proof.
 intros X [star|x]; trivial.
Defined.

Lemma lift_F_compose (X Y Z:Set) (g:X->Y) (f:Y->Z) bx: 
   (fun bx0 => lift_F_ Y Z f (lift_F_ X Y g bx0)) bx = lift_F_ X Z (fun x => f (g x)) bx.
Proof.
 intros X Y Z g f [start|x]; trivial.
Defined.

Lemma lift_F_extensionality: forall (X Y:Set) (f0 f1:X->Y) bx, (forall x, f0 x = f1 x) -> lift_F_  _ _ f0 bx = lift_F_ _ _ f1 bx.
Proof.
 intros X Y f0 f1 bx hyp_ext;
 unfold lift_F_; destruct bx as [star|x]; repeat rewrite hyp_ext; trivial.
Defined.

Record F_coalgebra : Type :=
{ states : Set 
; transition : states -> F_ states
}.


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

CoInductive maximal_bisimulation_conat (S1 S2:F_coalgebra) (s1:S1.(states)) (s2:S2.(states)) : Prop :=
    | max_bisim_conat_O : S1.(transition) s1 = inl S1.(states) tt -> S2.(transition) s2 = inl S2.(states) tt -> maximal_bisimulation_conat _ _ s1 s2
    | max_bisim_conat_S : forall s1' s2', S1.(transition) s1 = inr unit s1' -> S2.(transition) s2 = inr unit s2' -> maximal_bisimulation_conat _ _ s1' s2' -> maximal_bisimulation_conat _ _ s1 s2.

Definition maximal_bisimulation:= maximal_bisimulation_conat.

Lemma conat_transition_dec_inf:forall (S1:F_coalgebra) (s1:S1.(states)), 
   {star | S1.(transition) s1 = inl _ star} + { s1' | S1.(transition) s1 = inr unit s1'}.
Proof.
 intros [X_st X_tr] x.
 simpl in x.
 generalize (refl_equal (X_tr x)).
 pattern x at 1.
 destruct (X_tr x) as [star|x']; intros hyp.
  left; exists star; trivial.
  right; exists x'; trivial.
Defined. 

Definition maximal_bisimulation_conat_pred : forall (S1 S2:F_coalgebra), 
{s1s2 : S1.(states) * S2.(states)| maximal_bisimulation _ _ (fst s1s2) (snd s1s2)} -> 
unit + {s1s2 : S1.(states) * S2.(states)| maximal_bisimulation _ _ (fst s1s2) (snd s1s2)}.
Proof.
 intros S1 S2 [[x y] hyp]. 
 destruct (conat_transition_dec_inf S1 x) as [[starX hyp_trX]|[x' hyp_trX]].
  left; exact starX.
  right.
  destruct (conat_transition_dec_inf S2 y) as [[starY hyp_trY]|[y' hyp_trY]].
   apply False_rec.
   destruct hyp as [hyp_bis1 hyp_bis2|s1' s2' hyp_bis1 hyp_bis2]; simpl in hyp_bis1, hyp_bis2.
    rewrite hyp_bis1 in hyp_trX; discriminate hyp_trX.
    rewrite hyp_bis2 in hyp_trY; discriminate hyp_trY.
   
   exists (x',y'); simpl in *.
   destruct hyp as [hyp_bis1 hyp_bis2|s1' s2' hyp_bis1 hyp_bis2].
    rewrite hyp_bis1 in hyp_trX; discriminate hyp_trX.
    rewrite hyp_bis1 in hyp_trX; rewrite hyp_bis2 in hyp_trY.
    rewrite <- (inr_injection _ _ _ _ hyp_trX).
    rewrite <- (inr_injection _ _ _ _ hyp_trY).
    assumption.
Defined.

Lemma maximal_bisimulation_conat_pred_property1: forall (S1 S2:F_coalgebra) 
    (u:unit) s1 s2 (hyp: maximal_bisimulation _ _ s1 s2),
     S1.(transition) s1 = inl S1.(states) u ->
  maximal_bisimulation_conat_pred S1 S2 (exist (fun s1s2 =>
                                          maximal_bisimulation S1 S2 (fst s1s2) (snd s1s2)) (s1, s2) hyp) = 
  inl _ u. 
Proof.
 intros S1 S2 u x y hyp hyp1.
 unfold maximal_bisimulation_conat_pred.
 destruct (conat_transition_dec_inf S1 x) as [[starX hyp_trX]|[x' hyp_trX]].
  f_equal; induction starX; destruct u; reflexivity.
  apply False_ind; rewrite hyp1 in hyp_trX; discriminate hyp_trX.
Defined.


Lemma maximal_bisimulation_conat_pred_property2: forall (S1 S2:F_coalgebra) 
     s1 s2 (hyp: maximal_bisimulation _ _ s1 s2) s1' s2' (hyp': maximal_bisimulation _ _ s1' s2'),
     S1.(transition) s1 = inr unit s1' ->
     S2.(transition) s2 = inr unit s2' ->
  { hyp'' |  maximal_bisimulation_conat_pred S1 S2 (exist (fun s1s2 =>
                                          maximal_bisimulation S1 S2 (fst s1s2) (snd s1s2)) (s1, s2) hyp) = 
   inr unit (exist (fun s1s2 => maximal_bisimulation S1 S2 (fst s1s2) (snd s1s2)) (s1', s2') hyp'')}.
Proof.
 intros S1 S2 x y hyp s1' s2' hyp' hyp1 hyp2. 
 unfold maximal_bisimulation_conat_pred.
 destruct (conat_transition_dec_inf S1 x) as [[starX hyp_trX]|[x' hyp_trX]].
  apply False_ind; rewrite hyp1 in hyp_trX; discriminate hyp_trX.
  destruct (conat_transition_dec_inf S2 y) as [[starY hyp_trY]|[y' hyp_trY]].
   apply False_ind; rewrite hyp2 in hyp_trY; discriminate hyp_trY.

    assert (hyp_s1':x'=s1');
    [rewrite hyp1 in hyp_trX; rewrite <- (inr_injection _ _ _ _ hyp_trX); trivial|].
    assert (hyp_s2':y'=s2');
    [rewrite hyp2 in hyp_trY; rewrite <- (inr_injection _ _ _ _ hyp_trY); trivial|].
    rewrite <- hyp_s1' in hyp'; rewrite <- hyp_s2' in hyp'; rewrite <- hyp_s1'; rewrite <- hyp_s2'.
    exists (match hyp with
        | max_bisim_conat_O hyp_bis1 _ =>
            False_ind (maximal_bisimulation S1 S2 x' y')
              (eq_ind (inl (states S1) tt)
                 (fun e : F_ (states S1) =>
                  match e with
                  | inl _ => True
                  | inr _ => False
                  end) I (inr unit x')
                 (eq_ind (transition S1 x)
                    (fun f : F_ (states S1) => f = inr unit x') hyp_trX
                    (inl (states S1) tt) hyp_bis1))
        | max_bisim_conat_S s1'0 s2'0 hyp_bis1 hyp_bis2 hyp0 =>
            eq_ind s1'0
              (fun x'0 : states S1 => maximal_bisimulation S1 S2 x'0 y')
              (eq_ind s2'0
                 (fun y'0 : states S2 =>
                  maximal_bisimulation S1 S2 s1'0 y'0) hyp0 y'
                 (inr_injection (states S2) unit s2'0 y'
                    (eq_ind (transition S2 y)
                       (fun f : F_ (states S2) => f = inr unit y') hyp_trY
                       (inr unit s2'0) hyp_bis2))) x'
              (inr_injection (states S1) unit s1'0 x'
                 (eq_ind (transition S1 x)
                    (fun f : F_ (states S1) => f = inr unit x') hyp_trX
                    (inr unit s1'0) hyp_bis1))
        end).
   reflexivity.
Defined.



Lemma maximal_bisimulation_is_bisimulation: forall (S1 S2:F_coalgebra), is_F_bisimulation _ _ (maximal_bisimulation S1 S2).
Proof.
 intros S1 S2.
 exists (maximal_bisimulation_conat_pred S1 S2).
 intros [[x y] [hyp1 hyp2|s1' s2' hyp1 hyp2 hypR]].
 unfold lift_F_; split;
 rewrite (maximal_bisimulation_conat_pred_property1 _ _ tt x y (max_bisim_conat_O S1 S2 (fst (x, y)) (snd (x, y)) hyp1 hyp2) hyp1). 
  rewrite <- hyp1; reflexivity.
  rewrite <- hyp2; reflexivity.

  unfold lift_F_; split;
   destruct (maximal_bisimulation_conat_pred_property2 _ _ x y (max_bisim_conat_S _ _ (fst (x, y)) (snd (x, y)) s1' s2' hyp1 hyp2 hypR) s1' s2' hypR hyp1 hyp2) 
           as [hyp'' hyp''_prop];
   rewrite hyp''_prop; symmetry; assumption. 
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
  set (hyp:=projT2 h_coind).
  set (gamma:=projT1 h_coind).
  set (s1s2h:=existS (fun s1s2=> R' (fst s1s2) (snd s1s2)) (s1,s2) hyp').
  destruct (hyp s1s2h) as [hyp1 hyp2].
  clear hyp.
  unfold lift_F_ in hyp1,hyp2; simpl in hyp1, hyp2.
  change (match gamma s1s2h with
         | inl star => inl X star
         | inr x => inr unit (fst (projT1 x))
         end = X_tr s1) in hyp1.
  change (match gamma s1s2h with
         | inl star => inl Y star
         | inr x => inr unit (snd (projT1 x))
         end = Y_tr s2) in hyp2.
  destruct (gamma s1s2h) as [u|[[s1' s2'] hyp]].

   constructor 1; unfold states, transition; 
   [rewrite <- hyp1 |rewrite <- hyp2] ; f_equal; destruct u; reflexivity.


   constructor 2 with s1' s2';unfold states, transition;
   [rewrite <- hyp1 |rewrite <- hyp2| ]; [f_equal|f_equal|].

   apply (maximal_bisimulation_is_maximal _ _ R' h_coind); assumption.
Defined.

Definition weak_pullback (X Y Z:Set) (f:X->Z) (g:Y->Z):={ xy:(X*Y) | f(fst xy)=g(snd xy)}.

Definition wkpk_id_rht: forall (X Y Z:Set) (f:X->Z) (g:Y->Z), 
    weak_pullback _ _ _ (lift_F_ _ _ f) (lift_F_ _ _ g) -> F_ (weak_pullback _ _ _ f g).
Proof.
 intros X Y Z f g [[[ux|x] [uy|y]] h]; simpl in h; unfold F_.
  left; exact ux.
  left; exact ux.
  left; exact uy.
  right; exists (x,y); apply inr_injection with unit; exact h.
Defined.

Lemma F_pres_weak_pullback_arr: forall (X Y Z:Set) (f:X->Z) (g:Y->Z) 
                                  (wxy:weak_pullback _ _ _ (lift_F_ _ _ f) (lift_F_ _ _ g)), 
 lift_F_ (weak_pullback _ _ _ f g) X (fun xy=>fst (projT1 xy)) (wkpk_id_rht _ _ _ _ _ wxy) =  fst (projT1 wxy) /\
 lift_F_ (weak_pullback _ _ _ f g) Y (fun xy=>snd (projT1 xy)) (wkpk_id_rht _ _ _ _ _ wxy) =  snd (projT1 wxy). 
Proof.
 intros X Y Z f g [[[ux|x] [uy|y]] h]; simpl in h; unfold wkpk_id_rht, lift_F_; split; trivial; simpl;
 first [rewrite (inl_injection _ _ _ _ h); trivial|discriminate h].
Defined.


End Bisimulation_For_Coalgebra_CoPeano.


Module CoPeano_as_Weakly_Final_Coalgebra  <: Weakly_Final_Coalgebra.

Include Bisimulation_For_Coalgebra_CoPeano.

Module Import CoPeano_Coalgebra := Bisimulation_theory Bisimulation_For_Coalgebra_CoPeano.

Definition is_weakly_final (w:F_coalgebra) := forall (S0:F_coalgebra),
   { F_unfold_ : S0.(states) -> w.(states) | 
     forall s0, w.(transition) (F_unfold_ s0) = lift_F_ _ _ F_unfold_ (S0.(transition) s0)}.


Definition CoPeano := Build_F_coalgebra conat pred. 

Definition w:=CoPeano.

CoFixpoint CoPeano_unfold (S0:F_coalgebra) (s0: S0.(states)) : CoPeano.(states):=
     match S0.(transition) s0 with
     | inl star => co_O 
     | inr x => co_S (CoPeano_unfold S0 x)
     end.

Lemma CoPeano_unfold_unfolded:forall (S0:F_coalgebra) (s0: S0.(states)), CoPeano_unfold S0 s0 = 
     match S0.(transition) s0 with
     | inl star => co_O 
     | inr x => co_S (CoPeano_unfold S0 x)
     end.
Proof.
 intros S0 x.
 rewrite (unfold_conat (CoPeano_unfold S0 x)).
 destruct S0 as [X X_tr].
 unfold transition.
 remember (X_tr x) as X_tr_x;
 revert HeqX_tr_x;
 pattern (X_tr_x);
 destruct (X_tr_x) as [u | x']; intros hyp_X;simpl; rewrite <- hyp_X; reflexivity.
Defined.

Lemma commutativity_CoPeano_unfold  (S0: F_coalgebra) (x:S0.(states)) : 
       CoPeano.(transition) (CoPeano_unfold S0 x) = (lift_F_ _ _ (CoPeano_unfold S0)) (S0.(transition) x).
Proof.
 intros [X X_tr] x.
 unfold lift_F_; simpl.
 set (X_tr_x:=X_tr x). 
 destruct X_tr_x as [u|x']; trivial.
 destruct u; reflexivity.
Defined.

Lemma w_is_weakly_final:is_weakly_final w.
Proof.
 intros S0.
 exists (CoPeano_unfold S0).
 apply commutativity_CoPeano_unfold.
Defined.

Definition F_unfold (S0:F_coalgebra) := proj1_sig (w_is_weakly_final S0).
Definition commutativity_F_unfold (S0:F_coalgebra) :forall (x:S0.(states)), w.(transition) (F_unfold S0 x) = (lift_F_ _ _ (F_unfold S0)) (S0.(transition) x) := proj2_sig (w_is_weakly_final S0).
Definition bisimilar := maximal_bisimulation w w.

Notation " A (=) B " := (maximal_bisimulation w w A B) (at level 70).

Definition refl_bisimilar := refl_bisimilar w.

Definition sym_bisimilar := sym_bisimilar w.

Definition trans_bisimilar := trans_bisimilar w.

Lemma CoPeano_unfold_bisim_unique:forall (S0:F_coalgebra) f, 
   (forall (s0: S0.(states)), f s0 = match S0.(transition) s0 with
                                        | inl star => co_O 
                                        | inr x => co_S (f x)
                                        end) ->
        forall s, CoPeano_unfold S0 s(=) f s.
Proof.
 cofix.
 intros [X X_tr] f hyp x.
 rewrite (hyp x).
 unfold transition.
 remember (X_tr x) as X_tr_x;
 revert HeqX_tr_x;
 pattern (X_tr_x);
 destruct (X_tr_x) as [u | x']; intros hyp_X;simpl.

  constructor 1; trivial; simpl; rewrite <- hyp_X; trivial.
  constructor 2 with  (CoPeano_unfold (Build_F_coalgebra X X_tr) x') (f x'); simpl;
  [ rewrite <- hyp_X; reflexivity
  | reflexivity
  | apply (CoPeano_unfold_bisim_unique _ _ hyp)].
Defined.

Lemma CoPeano_unique_with_cons:forall (S0:F_coalgebra) f g, 
   (forall (s0: S0.(states)), (f s0) = match S0.(transition) s0 with
                                          | inl star => co_O 
                                          | inr x => co_S (f x)
                                          end)  -> 
   (forall (s0: S0.(states)), (g s0) = match S0.(transition) s0 with
                                          | inl star => co_O 
                                          | inr x => co_S (g x)
                                          end) -> forall s, 
        f s(=) g s.
Proof.
 intros S0 f g Hf Hg s0.
 apply trans_bisimilar with (CoPeano_unfold S0 s0); 
 [apply sym_bisimilar|]; apply CoPeano_unfold_bisim_unique ; assumption.
Defined.


Lemma F_unique:forall (S0:F_coalgebra) f g, 
   (forall (s0: S0.(states)), w.(transition) (f s0) = (lift_F_ _ _ f) (S0.(transition) s0) ) ->
   (forall (s0: S0.(states)), w.(transition) (g s0) = (lift_F_ _ _ g) (S0.(transition) s0) ) ->
   forall s, f s(=) g s.
Proof.
 intros S0 f g; simpl; unfold lift_F_; intros Hf Hg.
 apply CoPeano_unique_with_cons; intros s; assert (Hfs:=Hf s);assert (Hgs:=Hg s); destruct S0 as [S0_st S0_tr]; simpl in *;
 [ destruct (S0_tr s) as [u|x']; [ apply pred_inl_co_O with u| apply pred_inr_co_S]
 | destruct (S0_tr s) as [u|x']; [ apply pred_inl_co_O with u| apply pred_inr_co_S]
 ]; symmetry; trivial.
Defined.


Lemma lift_F_extensionality_bisim_CoPeano: forall (X:Set) (f0 f1:X->CoPeano.(states)) bx, (forall x, f0 x (=) f1 x) -> 
    match bx with 
    | inl starX => lift_F_  _ _ f0 bx = inl _ tt /\ lift_F_  _ _ f1 bx=inl _ tt 
    | inr b_x' =>  exists s1', exists  s2', lift_F_  _ _ f0 bx = inr unit s1' /\  lift_F_  _ _ f1 bx = inr _ s2' /\ s1' (=) s2'
    end.
Proof.
 intros X f0 f1 bx hyp_ext.
 unfold lift_F_.
 destruct bx as [u|x']. 
  split; destruct u; trivial.
  exists (f0 x'); exists (f1 x'); repeat split; trivial.
Defined.


Lemma rel_image_lift_F_CoPeano_bisimilar_spelled: forall (b_x b_y: F_ CoPeano.(states)),  
     rel_image_lift_F_ _ _ bisimilar b_x b_y <-> match b_x, b_y with 
                                                 | inl starX, inl starY => starX = starY
                                                 | inr b_x', inr b_y' => co_S b_x' (=) co_S b_y'
                                                 | _, _ =>  False
                                                 end.
Proof.
 intros [ux|x] [uy|y]; simpl; unfold rel_image_lift_F_; split; simpl; intros hyp.

  destruct ux; destruct uy; reflexivity...
  exists co_O; exists co_O; repeat split; simpl.
   constructor 1; simpl; trivial.
   destruct ux; destruct uy; reflexivity.
   destruct ux; destruct uy; reflexivity...
  destruct hyp as [x [y' [hyp [hyp1 hyp2]]]].
  inversion hyp as [hyp3 hyp4|s1' s2' hyp3 hyp4 hyp5]; simpl in *.
   rewrite <- hyp2 in hyp4; discriminate hyp4.
   rewrite <- hyp1 in hyp3; discriminate hyp3...
  contradiction...
  destruct hyp as [x' [y [hyp [hyp1 hyp2]]]].
  inversion hyp as [hyp3 hyp4|s1' s2' hyp3 hyp4 hyp5]; simpl in *.
   rewrite <- hyp1 in hyp3; discriminate hyp3.
   rewrite <- hyp2 in hyp4; discriminate hyp4...
  contradiction...
  destruct hyp as [x' [y' [hyp [hyp1 hyp2]]]];
   replace (co_S x) with x'; [replace (co_S y) with y'; trivial|]; apply pred_inr_co_S; assumption...
  exists (co_S x); exists (co_S y); repeat split; simpl; assumption.
Defined.
 
Lemma lift_F_extensionality_bisim: forall (X:Set) (f0 f1:X->w.(states)) bx, (forall x, f0 x (=) f1 x) -> rel_image_lift_F_ _ _ bisimilar (lift_F_  _ _ f0 bx) (lift_F_ _ _ f1 bx).
Proof.
 intros X f0 f1 bx hyp_eq.
 apply <- rel_image_lift_F_CoPeano_bisimilar_spelled.
 generalize (lift_F_extensionality_bisim_CoPeano _ f0 f1 bx hyp_eq).  
 destruct bx as [u|bx']; fold w.
  intros [hyp1 hyp2]; rewrite hyp1; rewrite hyp2; trivial.
  intros (s1' & s2' & hyp1 & hyp2 & hyp3). 
  rewrite hyp1; rewrite hyp2.
  constructor 2 with s1' s2'; simpl; trivial.
Defined.

End CoPeano_as_Weakly_Final_Coalgebra.
