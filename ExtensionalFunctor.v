(************************************************************************)
(* Copyright 2008 Milad Niqui                                           *)
(* This file is distributed under the terms of the                      *)
(* GNU Lesser General Public License Version 3                          *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses/lgpl-3.0.html>         *)
(************************************************************************)

(** Module type for extensional functors, and some parametrised
modules for basic functor cosntructs. *)

Module Type Set_Functor.

Parameter F_ : Set -> Set.

Parameter lift_F_ :forall (X Y:Set) (f:X->Y), F_ X -> F_ Y.

Axiom lift_F_id :forall X (fx: F_ X), fx = lift_F_ X X (fun x0 : X => x0) fx.

Axiom lift_F_compose:forall (X Y Z:Set) (g:X->Y) (f:Y->Z) fx, 
   (fun fx0 => lift_F_ Y Z f (lift_F_ X Y g fx0)) fx = lift_F_ X Z (fun x => f (g x)) fx.

Axiom lift_F_extensionality: forall (X Y:Set) (f0 f1:X->Y) fx, (forall x, f0 x = f1 x) -> lift_F_  _ _ f0 fx = lift_F_ _ _ f1 fx.

End Set_Functor.


Module Set_Functor_Iter_theory (MF:Set_Functor).

Import MF.

Fixpoint F_iter (j:nat) : Set -> Set := 
   match j with
   |   O  => fun X => X
   | S j' => fun X => (F_iter j' (F_ X))
   end. 

Fixpoint lift_F_iter (X Y:Set) (f:X->Y) j  {struct j} : F_iter j X -> F_iter j Y :=
   match j as n return (F_iter n X -> F_iter n Y) with
   |   O  => f
   | S j' =>  lift_F_iter (F_ X) (F_ Y) (lift_F_ _ _ f) j' 
   end.

Lemma F_iter_S (X:Set) (j:nat): F_ (F_iter j X)= F_iter (S j) X.
Proof. 
 revert X; induction j.
  reflexivity.
  intros X; simpl; rewrite IHj; reflexivity.
Qed.

Lemma lift_F_iter_extensionality: forall (X Y:Set) (f0 f1:X->Y) j s_ix, (forall x, f0 x = f1 x) -> lift_F_iter _ _ f0 j s_ix = lift_F_iter _ _ f1 j s_ix.
Proof.
 intros X Y f0 f1 j; revert X Y f0 f1; induction j; intros X Y f0 f1 s_ix hyp_ext.
  simpl; apply hyp_ext.
  simpl.
  rewrite (IHj (F_ X) (F_ Y) (lift_F_ X Y f0) (lift_F_ X Y f1) s_ix).
   trivial.
   intros sx.
   apply (lift_F_extensionality X Y f0 f1 sx hyp_ext).
Qed.

Lemma lift_F_iter_compose (X Y Z:Set) (g:X->Y) (f:Y->Z) j s_ix:
 lift_F_iter Y Z f j (lift_F_iter X Y g j s_ix) = lift_F_iter X Z (fun x => f (g x)) j s_ix.
Proof.
 revert X Y Z g f s_ix.
 induction j; intros X Y Z g f s_ix. 
  simpl; trivial.
  simpl.
  rewrite IHj.
  apply lift_F_iter_extensionality.
  apply (lift_F_compose X Y Z g f).
Qed.

Lemma lift_F_iter_id (X:Set) j (fx:F_iter j X): fx = lift_F_iter X X (fun x0 : X => x0) j fx.
Proof.
 revert X fx.
 induction j; intros X fx. 
  simpl; trivial.
  simpl in *.
  transitivity (lift_F_iter (F_ X) (F_ X) (fun x0 : F_ X => x0) j fx).
   apply IHj. 
   apply lift_F_iter_extensionality.  
   apply lift_F_id.
Qed.

End Set_Functor_Iter_theory.

Close Scope nat_scope.


(* ################################################################################ *)
(** Constant functor: sending every arrow to the identity arrow *)
(* ################################################################################ *)

Module Type Set_module_argument.

Parameter U:Set.

End Set_module_argument.

Module constant_as_Set_Functor (Import U:Set_module_argument) <: Set_Functor.

Export U.

Definition F_ (X:Set) := U.

Definition lift_F_ (X Y:Set) (f:X->Y) (fx:F_ X) : F_ Y := fx.

Lemma lift_F_id :forall X (fx: F_ X), fx = lift_F_ X X (fun x0 : X => x0) fx.
Proof.
 intros X u; unfold lift_F_; reflexivity.
Qed.

Lemma lift_F_compose (X Y Z:Set) (g:X->Y) (f:Y->Z) fx: 
   (fun fx0 => lift_F_ Y Z f (lift_F_ X Y g fx0)) fx = lift_F_ X Z (fun x => f (g x)) fx.
Proof.
 unfold lift_F_; reflexivity.
Qed.

Lemma lift_F_extensionality: forall (X Y:Set) (f0 f1:X->Y) fx, (forall x, f0 x = f1 x) -> lift_F_  _ _ f0 fx = lift_F_ _ _ f1 fx.
Proof.
 intros X Y g f u hyp; unfold lift_F_; reflexivity. 
Qed.

End constant_as_Set_Functor.


(* ################################################################################ *)
(** Identity functor *)
(* ################################################################################ *)

Module identity_as_Set_Functor <: Set_Functor.

Definition F_ (X:Set) := X.

Definition lift_F_ (X Y:Set) (f:X->Y) (fx:F_ X) : F_ Y := f fx.

Lemma lift_F_id :forall X (fx: F_ X), fx = lift_F_ X X (fun x0 : X => x0) fx.
Proof.
 intros X u; unfold lift_F_; reflexivity.
Qed.

Lemma lift_F_compose (X Y Z:Set) (g:X->Y) (f:Y->Z) fx: 
   (fun fx0 => lift_F_ Y Z f (lift_F_ X Y g fx0)) fx = lift_F_ X Z (fun x => f (g x)) fx.
Proof.
 unfold lift_F_; reflexivity.
Qed.

Lemma lift_F_extensionality: forall (X Y:Set) (f0 f1:X->Y) fx, (forall x, f0 x = f1 x) -> lift_F_  _ _ f0 fx = lift_F_ _ _ f1 fx.
Proof.
 intros X Y g f u hyp; unfold lift_F_; apply hyp. 
Qed.

End identity_as_Set_Functor.


(* ################################################################################ *)
(** Coproduct *)
(* ################################################################################ *)

Module coproduct_as_Set_Functor (FA:Set_Functor) (FB:Set_Functor) <: Set_Functor.

Definition FA_:=FA.F_.
Definition FB_:=FB.F_.


Definition F_ (X:Set) := (FA_ X) + (FB_ X).

Definition lift_F_ (X Y:Set) (f:X->Y) (fx:F_ X) : F_ Y :=
       match fx with
       | inl fa => inl (FB_ Y) (FA.lift_F_ X Y f fa)
       | inr fb => inr (FA_ Y) (FB.lift_F_ X Y f fb)
       end.

Lemma lift_F_id :forall X (fx: F_ X), fx = lift_F_ X X (fun x0 : X => x0) fx.
Proof.
 intros X [fa|fb]; unfold lift_F_;
 [ rewrite <- (FA.lift_F_id X) | rewrite <- (FB.lift_F_id X)]; reflexivity.
Qed.

Lemma lift_F_compose (X Y Z:Set) (g:X->Y) (f:Y->Z) fx: 
   (fun fx0 => lift_F_ Y Z f (lift_F_ X Y g fx0)) fx = lift_F_ X Z (fun x => f (g x)) fx.
Proof.
 destruct fx as [fa|fb]; unfold lift_F_;
 [ rewrite FA.lift_F_compose | rewrite FB.lift_F_compose] ; reflexivity.
Qed.

Lemma lift_F_extensionality: forall (X Y:Set) (f0 f1:X->Y) fx, (forall x, f0 x = f1 x) -> lift_F_  _ _ f0 fx = lift_F_ _ _ f1 fx.
Proof.
 intros X Y g f [fa|fb] hyp; unfold lift_F_; f_equal;
 [ apply FA.lift_F_extensionality | apply FB.lift_F_extensionality]; assumption.
Qed.

End coproduct_as_Set_Functor.

(* ################################################################################ *)
(** Product *)
(* ################################################################################ *)

Module product_as_Set_Functor (FA:Set_Functor) (FB:Set_Functor) <: Set_Functor.

Definition FA_:=FA.F_.
Definition FB_:=FB.F_.


Definition F_ (X:Set) := (FA_ X) * (FB_ X).

Definition lift_F_ (X Y:Set) (f:X->Y) (fx:F_ X) : F_ Y := let (fa, fb) := fx in (FA.lift_F_ X Y f fa, FB.lift_F_ X Y f fb).

Lemma lift_F_id :forall X (fx: F_ X), fx = lift_F_ X X (fun x0 : X => x0) fx.
Proof.
 intros X [fa fb]; unfold lift_F_;
 rewrite <- (FA.lift_F_id X); rewrite <- (FB.lift_F_id X); reflexivity.
Qed.

Lemma lift_F_compose (X Y Z:Set) (g:X->Y) (f:Y->Z) fx: 
   (fun fx0 => lift_F_ Y Z f (lift_F_ X Y g fx0)) fx = lift_F_ X Z (fun x => f (g x)) fx.
Proof.
 destruct fx as [fa fb]; unfold lift_F_;
 rewrite FA.lift_F_compose; rewrite FB.lift_F_compose; reflexivity.
Qed.

Lemma lift_F_extensionality: forall (X Y:Set) (f0 f1:X->Y) fx, (forall x, f0 x = f1 x) -> lift_F_  _ _ f0 fx = lift_F_ _ _ f1 fx.
Proof.
 intros X Y g f [fa fb] hyp; unfold lift_F_; f_equal;
 [ apply FA.lift_F_extensionality | apply FB.lift_F_extensionality]; assumption.
Qed.

End product_as_Set_Functor.


(* ################################################################################ *)
(** Composition *)
(* ################################################################################ *)

Module composition_as_Set_Functor (FA:Set_Functor) (FB:Set_Functor) <: Set_Functor.


Definition FA_:=FA.F_.
Definition FB_:=FB.F_.


Definition F_ (X:Set) := FA_ (FB_ X).


Definition lift_F_ (X Y:Set) (f:X->Y) : F_ X -> F_ Y :=  FA.lift_F_ (FB_ X) (FB_ Y) (FB.lift_F_ X Y f).


Lemma lift_F_id :forall X (fx: F_ X), fx = lift_F_ X X (fun x0 : X => x0) fx.
Proof.
 intros X fx; trivial.
 unfold lift_F_.
 transitivity (FA.lift_F_ (FB_ X) (FB_ X) (fun x0 : FB_ X => x0) fx); [apply FA.lift_F_id|].
 apply FA.lift_F_extensionality.  
 apply FB.lift_F_id.
Qed.

Lemma lift_F_compose (X Y Z:Set) (g:X->Y) (f:Y->Z) fx: 
   (fun fx0 => lift_F_ Y Z f (lift_F_ X Y g fx0)) fx = lift_F_ X Z (fun x => f (g x)) fx.
Proof.
 unfold lift_F_.
 rewrite FA.lift_F_compose.
 apply FA.lift_F_extensionality.
 apply FB.lift_F_compose.
Qed.

Lemma lift_F_extensionality: forall (X Y:Set) (f0 f1:X->Y) fx, (forall x, f0 x = f1 x) -> lift_F_  _ _ f0 fx = lift_F_ _ _ f1 fx.
Proof.
 intros X Y g f fx hyp.
 unfold lift_F_.
 apply FA.lift_F_extensionality.
 intros x.
 apply FB.lift_F_extensionality.
 assumption.
Qed.

End composition_as_Set_Functor.


(* ################################################################################ *)
(** Iteration *)
(* ################################################################################ *)

Module Type nat_module_argument.

Parameter n:nat.

End nat_module_argument.


Module iteration_as_Set_Functor (FA:Set_Functor) (Import n:nat_module_argument) <: Set_Functor.

Export n.

Definition FA_:=FA.F_.

Module F_theory:=Set_Functor_Iter_theory FA.

Definition F_ (X:Set) := F_theory.F_iter n X.

Definition lift_F_ (X Y:Set) (f:X->Y) : F_ X -> F_ Y := F_theory.lift_F_iter X Y f n.

Lemma lift_F_id :forall X (fx: F_ X), fx = lift_F_ X X (fun x0 : X => x0) fx.
Proof.
 intros X fx; unfold lift_F_; apply F_theory.lift_F_iter_id. 
Qed.

Lemma lift_F_compose (X Y Z:Set) (g:X->Y) (f:Y->Z) fx: 
   (fun fx0 => lift_F_ Y Z f (lift_F_ X Y g fx0)) fx = lift_F_ X Z (fun x => f (g x)) fx.
Proof.
 unfold lift_F_; apply F_theory.lift_F_iter_compose.
Qed.

Lemma lift_F_extensionality: forall (X Y:Set) (f0 f1:X->Y) fx, (forall x, f0 x = f1 x) -> lift_F_  _ _ f0 fx = lift_F_ _ _ f1 fx.
Proof.
 intros X Y g f fx hyp;  unfold lift_F_; apply F_theory.lift_F_iter_extensionality; assumption.
Qed.

End iteration_as_Set_Functor.
