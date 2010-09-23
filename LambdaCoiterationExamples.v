(************************************************************************)
(* Copyright 2008-2010 Milad Niqui                                      *)
(* This file is distributed under the terms of the                      *)
(* GNU Lesser General Public License Version 3                          *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses/lgpl-3.0.html>         *)
(************************************************************************)

(** Some examples illustrating the use of lambda-coiteration scheme.
*)

Require Import IntensionalLambdaBisimulation.
Require Import ZStreamCoalgebra.

(* Some useful fucntors. *)

(* X |------> X x X *)

Module Pairing_Functor:=product_as_Set_Functor identity_as_Set_Functor identity_as_Set_Functor.


(* X |------> B x X x X *)

Module B_Set_module_argument <: Set_module_argument.
Definition U:=B.
End B_Set_module_argument.

Module B_constant_as_Set_Functor:= constant_as_Set_Functor B_Set_module_argument.

Module B_Pairing_Functor:=product_as_Set_Functor B_constant_as_Set_Functor Pairing_Functor.


(* X |------> (B -> B) * X *)

Module B_arr_B_Set_module_argument <: Set_module_argument.
Definition U:=B->B.
End B_arr_B_Set_module_argument.

Module B_arr_B_constant_as_Set_Functor:= constant_as_Set_Functor B_arr_B_Set_module_argument.

Module B_map_S_Functor := product_as_Set_Functor B_arr_B_constant_as_Set_Functor identity_as_Set_Functor.


(*XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX*)
(* Some examples *)
(*XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX*)

Module Import Streams_Conv_LamCoiter := Lambda_Bisimulation_theory Streams_as_Weakly_Final_Coalgebra Pairing_Functor.

Lemma commutativity_Conv_fst_snd (Lambda:T_over_B_distributive) (BS: BT_coalgebroid) (x:BS.(bs_states)) : 
 fst (Str.(transition) (Lam_coiterator Lambda BS x)) =
 fst( lift_B_ _ _ (Beta Lambda) (lift_B_ _ _  (lift_T_ _ _ (Lam_coiterator Lambda BS)) (bs_transition BS x))) /\
 snd (Str.(transition) (Lam_coiterator Lambda BS x)) (=) 
 snd( lift_B_ _ _ (Beta Lambda) (lift_B_ _ _  (lift_T_ _ _ (Lam_coiterator Lambda BS)) (bs_transition BS x))).
Proof.
 apply -> rel_image_lift_F_Str_bisimilar_spelled.
 apply commutativity_Lam_coiterator_rel_image_lifting.
Defined.


Lemma commutativity_Conv_hd_tl (Lambda:T_over_B_distributive) (BS: BT_coalgebroid) (x:BS.(bs_states)) : 
 hd (Lam_coiterator Lambda BS x) = fst (lift_B_ _ _ (Beta Lambda) (lift_B_ _ _  (lift_T_ _ _ (Lam_coiterator Lambda BS)) (bs_transition BS x))) /\
 tl (Lam_coiterator Lambda BS x) (=) snd( lift_B_ _ _ (Beta Lambda) (lift_B_ _ _  (lift_T_ _ _ (Lam_coiterator Lambda BS)) (bs_transition BS x))).
Proof.
 revert Lambda BS x.
 apply commutativity_Conv_fst_snd.
Defined.

Lemma commutativity_Conv_Cons_1 (Lambda:T_over_B_distributive) (BS: BT_coalgebroid) (x:BS.(bs_states)) : 
 Lam_coiterator Lambda BS x (=) Cons (fst (lift_B_ _ _ (Beta Lambda) (lift_B_ _ _  (lift_T_ _ _ (Lam_coiterator Lambda BS)) (bs_transition BS x))))
                           (snd (lift_B_ _ _ (Beta Lambda) (lift_B_ _ _  (lift_T_ _ _ (Lam_coiterator Lambda BS)) (bs_transition BS x)))).
Proof.
 rewrite (hd_tl_id (Lam_coiterator Lambda BS x)).
 destruct (commutativity_Conv_hd_tl Lambda BS x) as [hyp_hd hyp_tl].
 constructor.
  rewrite hyp_hd; reflexivity.
  unfold tl at 1.
  match goal with 
  | [ id1 : ?X1 (=) ?X2  |- _ ] => apply trans_bisimilar with X2; trivial
  end.
  apply refl_bisimilar. 
Defined.

Lemma commutativity_Conv_Cons_2 (Lambda:T_over_B_distributive) (BS: BT_coalgebroid) (x:BS.(bs_states)) : 
 Lam_coiterator Lambda BS x (=) Cons (fst (lift_B_ _ _ (fun s0=>Beta Lambda (lift_T_ _ _ (Lam_coiterator Lambda BS) s0)) (BS.(bs_transition) x)))
                           (snd (lift_B_ _ _ (fun s0 => Beta Lambda (lift_T_ _ _ (Lam_coiterator Lambda BS) s0)) (BS.(bs_transition) x))).
Proof.
 rewrite <- lift_B_compose with (Y:=T_ (Str.(states))).
 apply commutativity_Conv_Cons_1.
Defined.

Section Example_convolution.

(** Example:

Two types of convolution products:

<<
(x:xs) (X) (y:ys) = x.y : xs (X) (y:ys)   (+)   (x:xs) (X) ys 

(x:xs) (.) (y:ys) = x.y : xs (.) (y:ys)   (+)   (x:zeros) (.) ys 
                    
zeros = 0 : zeros
>>

*)

Require Import ZArith.
Open Scope Z_scope.

Definition lambda_convolution (X:Set) (sbx:T_ (B_ X)) : B_ (T_ X) := ( fst (fst sbx)+ fst (snd sbx) , (snd (fst sbx), snd (snd sbx)) ).

Lemma lambda_convolution_natural: forall (X Y : Set) (f : X -> Y) (sbx : T_ (B_ X)),
    lambda_convolution Y (lift_T_ (B_ X) (B_ Y) (lift_B_ X Y f) sbx) =  lift_B_ (T_ X) (T_ Y) (lift_T_ X Y f) (lambda_convolution X sbx).
Proof.
 intros X Y f [[b0 x0] [b1 x1]]; trivial. 
Defined.


Definition Lambda_convolution:T_over_B_distributive := Build_T_over_B_distributive lambda_convolution lambda_convolution_natural.

Definition pointwise_plus xs ys := Beta Lambda_convolution (xs,ys).


CoFixpoint enumFrom:Z->(Stream Z):=fun n => (Cons n (enumFrom (n+1))).


Definition test_str1:=enumFrom 0.
Definition test_str2:=enumFrom 10.
Fixpoint take (n:nat) (xs: Stream Z) {struct n} : List.list Z :=
  match n with 
  | O => List.nil
  | S n => List.cons (hd xs) (take n (tl xs))
  end.

Lemma pointwise_plus_cofixed :forall xs ys, pointwise_plus xs ys = 
                               Cons ((hd xs)+(hd ys)) (pointwise_plus (tl xs) (tl ys)).
Proof.
 intros xs ys.
 unfold pointwise_plus, Beta, Lambda_convolution, F_unfold.
 simpl; rewrite Str_unfold_unfolded.
 reflexivity.
Defined.


Section shuffle_product.
(**

<<
(x:xs) (X) (y:ys) = x.y : xs (X) (y:ys)   (+)   (x:xs) (X) ys 
>>
*)

Definition coalgebra_shuffle: BT_coalgebroid := 
   Build_BT_coalgebroid (B_pow_inf * B_pow_inf)
                      (fun b0s_b1s : B_pow_inf * B_pow_inf =>
                       match b0s_b1s with
                       | (Cons x xs, Cons y ys) => (x * y, (xs, Cons y ys, (Cons x xs, ys)))
                       end).


Definition shuffle_product xs ys:=Lam_coiterator Lambda_convolution coalgebra_shuffle (xs,ys).

Lemma shuffle_product_cofixed :forall xs ys, shuffle_product xs ys (=) 
                               Cons ((hd xs)*(hd ys)) (pointwise_plus (shuffle_product (tl xs) ys) (shuffle_product xs (tl ys))).
Proof.
 intros xs ys;
 assert (hyp_bis:=commutativity_Conv_Cons_1 Lambda_convolution coalgebra_shuffle (xs,ys));
 match goal with 
 | [ id1 : ?X1 (=) ?X2  |- _ ] => apply trans_bisimilar with X2
 end; 
 [ assumption
 |   destruct xs as [x xs']; destruct ys as [y ys']; apply refl_bisimilar
 ].
Defined.

End shuffle_product.

Section convolution_product.

(*
<<
(x:xs) (.) (y:ys) = x.y : xs (.) (y:ys)   (+)   (x:zeros) (.) ys 

zeros = 0 : zeros
>>

*)

(* This works if B has 0 (it is at least a semi-ring). *)

Definition ZeroB : B :=0.

Definition zeros : B_pow_inf := Streams_as_Weakly_Final_Coalgebra.F_unfold (Streams_as_Weakly_Final_Coalgebra.Build_F_coalgebra unit (fun t=>(ZeroB,t))) tt.

Lemma zeros_cofixed: zeros = Cons ZeroB zeros.
Proof.
 unfold zeros, F_unfold; simpl; rewrite Str_unfold_unfolded at 1; trivial.
Defined.

Definition coalgebra_convolution: BT_coalgebroid := 
   Build_BT_coalgebroid (B_pow_inf * B_pow_inf)
                      (fun b0s_b1s : B_pow_inf * B_pow_inf =>
                       match b0s_b1s with
                       | (Cons x xs, Cons y ys) => (x * y, (xs, Cons y ys, (Cons x zeros, ys)))
                       end).

Definition convolution_product xs ys:=Lam_coiterator Lambda_convolution coalgebra_convolution (xs,ys).

Lemma convolution_product_cofixed :forall xs ys, convolution_product xs ys (=) 
                  Cons ((hd xs)*(hd ys)) (pointwise_plus (convolution_product (tl xs) ys) (convolution_product (Cons (hd xs) zeros) (tl ys))).
Proof.
 intros xs ys;
 assert (hyp_bis:=commutativity_Conv_Cons_1 Lambda_convolution coalgebra_convolution (xs,ys));
 match goal with 
 | [ id1 : ?X1 (=) ?X2  |- _ ] => apply trans_bisimilar with X2
 end;
 [ assumption
 | destruct xs as [x xs']; destruct ys as [y ys']; apply refl_bisimilar
 ].
Defined.

End convolution_product.

(*
Time Eval vm_compute in (take 10  (pointwise_plus test_str1 test_str2)).
Time Eval vm_compute in (take 10  (shuffle_product test_str1 test_str2)).
Time Eval vm_compute in (take 10  (convolution_product test_str1 test_str2)).
*)
(* [shuffle]       = 0 :: 10 :: 42 :: 132 :: 368 :: 960 :: 2400 :: 5824 :: 13824 :: 32256 :: nil *)
(* [convolution]   = 0 :: 10 :: 31 :: 64 :: 110 :: 170 :: 245 :: 336 :: 444 :: 570 :: nil *)


End Example_convolution.

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

Section Example_pow.
(** Example:

<<
pow = 1 : pow (+) pow
>>

*)
Open Scope Z_scope.


Definition lambda_pow := lambda_convolution. 

Definition lambda_pow_natural := lambda_convolution_natural.

Definition Lambda_pow:T_over_B_distributive := Lambda_convolution.

Definition coalgebra_pow: BT_coalgebroid := Build_BT_coalgebroid unit (fun t : unit => ( 1, (t,t))).

Definition pow:=Lam_coiterator Lambda_convolution coalgebra_pow tt.

(*
Time Eval vm_compute in (take 16 pow).
*)

Lemma pow_cofixed : pow (=) Cons 1 (pointwise_plus pow pow).
Proof.
 assert (hyp_bis:=commutativity_Conv_Cons_1 Lambda_pow coalgebra_pow tt);
 match goal with 
 | [ id1 : ?X1 (=) ?X2  |- _ ] => apply trans_bisimilar with X2
 end; 
 [ assumption
 | apply refl_bisimilar
 ].
Defined.

End Example_pow.



Module Import Streams_map_S_LamCoiter := Lambda_Coiteration_theory Streams_as_Weakly_Final_Coalgebra B_map_S_Functor.

Lemma commutativity_map_S_fst_snd (Lambda:T_over_B_distributive) (BS: BT_coalgebroid) (x:BS.(bs_states)) : 
 fst (Str.(transition) (Lam_coiterator Lambda BS x)) =
 fst( lift_B_ _ _ (Beta Lambda) (lift_B_ _ _  (lift_T_ _ _ (Lam_coiterator Lambda BS)) (bs_transition BS x))) /\
 snd (Str.(transition) (Lam_coiterator Lambda BS x)) (=) 
 snd( lift_B_ _ _ (Beta Lambda) (lift_B_ _ _  (lift_T_ _ _ (Lam_coiterator Lambda BS)) (bs_transition BS x))).
Proof.
 apply -> rel_image_lift_F_Str_bisimilar_spelled.
 apply commutativity_Lam_coiterator_rel_image_lifting.
Defined.


Lemma commutativity_map_S_hd_tl (Lambda:T_over_B_distributive) (BS: BT_coalgebroid) (x:BS.(bs_states)) : 
 hd (Lam_coiterator Lambda BS x) = fst (lift_B_ _ _ (Beta Lambda) (lift_B_ _ _  (lift_T_ _ _ (Lam_coiterator Lambda BS)) (bs_transition BS x))) /\
 tl (Lam_coiterator Lambda BS x) (=) snd( lift_B_ _ _ (Beta Lambda) (lift_B_ _ _  (lift_T_ _ _ (Lam_coiterator Lambda BS)) (bs_transition BS x))).
Proof.
 apply (commutativity_map_S_fst_snd Lambda BS x).
Defined.

Lemma commutativity_map_S_Cons_1 (Lambda:T_over_B_distributive) (BS: BT_coalgebroid) (x:BS.(bs_states)) : 
 Lam_coiterator Lambda BS x (=) Cons (fst (lift_B_ _ _ (Beta Lambda) (lift_B_ _ _  (lift_T_ _ _ (Lam_coiterator Lambda BS)) (bs_transition BS x))))
                           (snd (lift_B_ _ _ (Beta Lambda) (lift_B_ _ _  (lift_T_ _ _ (Lam_coiterator Lambda BS)) (bs_transition BS x)))).
Proof.
 rewrite (hd_tl_id (Lam_coiterator Lambda BS x)).
 destruct (commutativity_map_S_hd_tl Lambda BS x) as [hyp_hd hyp_tl].
 constructor.
  rewrite hyp_hd; reflexivity.
  unfold tl at 1.
  match goal with 
  | [ id1 : ?X1 (=) ?X2  |- _ ] => apply trans_bisimilar with X2; trivial
  end.
  apply refl_bisimilar. 
Defined.

Section Example_map_S.


(** Example:

<<
nats = 0 :: map S nats
>>

*)

Open Scope Z_scope.


Definition lambda_map_S (X:Set) (sbx:T_ (B_ X)) : B_ (T_ X):=
       let (g, tmp) := sbx in let (b, x) := tmp in (g b,(g,x)).


Lemma lambda_map_S_natural: forall (X Y : Set) (f : X -> Y) (sbx : T_ (B_ X)),
    lambda_map_S Y (lift_T_ (B_ X) (B_ Y) (lift_B_ X Y f) sbx) =  lift_B_ (T_ X) (T_ Y) (lift_T_ X Y f) (lambda_map_S X sbx).
Proof.
 intros X Y f [phi [b x]]; trivial. 
Defined.
 
Definition Lambda_map_S:T_over_B_distributive := Build_T_over_B_distributive lambda_map_S lambda_map_S_natural.

Definition coalgebra_map_S: BT_coalgebroid := Build_BT_coalgebroid unit (fun t : unit => (0,(fun x=>x+1,tt))).

Definition nats:=Lam_coiterator Lambda_map_S coalgebra_map_S tt.

(*
Time Eval vm_compute in (take 10 nats).
*)


Definition map_ g xs := Beta Lambda_map_S (g,xs).


Lemma map__cofixed :forall g xs, map_ g xs = Cons (g (hd xs)) (map_ g (tl xs)).
Proof.
 intros g xs.
 unfold map_, Beta, Lambda_map_S, F_unfold.
 simpl; rewrite Str_unfold_unfolded.
 reflexivity.
Defined.

Lemma nats_cofixed : nats (=)  Cons 0 (map_ (fun x=>x+1) nats).
Proof.
 assert (hyp_bis:=commutativity_map_S_Cons_1 Lambda_map_S coalgebra_map_S tt);
 match goal with 
 | [ id1 : ?X1 (=) ?X2  |- _ ] => apply trans_bisimilar with X2
 end; 
 [ assumption
 | apply refl_bisimilar
 ].
Defined.

End Example_map_S.

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

Module Import Streams_Fib_LamCoiter := Lambda_Coiteration_theory Streams_as_Weakly_Final_Coalgebra B_Pairing_Functor.

Lemma commutativity_Fib_fst_snd (Lambda:T_over_B_distributive) (BS: BT_coalgebroid) (x:BS.(bs_states)) : 
 fst (Str.(transition) (Lam_coiterator Lambda BS x)) =
 fst( lift_B_ _ _ (Beta Lambda) (lift_B_ _ _  (lift_T_ _ _ (Lam_coiterator Lambda BS)) (bs_transition BS x))) /\
 snd (Str.(transition) (Lam_coiterator Lambda BS x)) (=) 
 snd( lift_B_ _ _ (Beta Lambda) (lift_B_ _ _  (lift_T_ _ _ (Lam_coiterator Lambda BS)) (bs_transition BS x))).
Proof.
 apply -> rel_image_lift_F_Str_bisimilar_spelled.
 apply commutativity_Lam_coiterator_rel_image_lifting.
Defined.


Lemma commutativity_Fib_hd_tl (Lambda:T_over_B_distributive) (BS: BT_coalgebroid) (x:BS.(bs_states)) : 
 hd (Lam_coiterator Lambda BS x) = fst (lift_B_ _ _ (Beta Lambda) (lift_B_ _ _  (lift_T_ _ _ (Lam_coiterator Lambda BS)) (bs_transition BS x))) /\
 tl (Lam_coiterator Lambda BS x) (=) snd( lift_B_ _ _ (Beta Lambda) (lift_B_ _ _  (lift_T_ _ _ (Lam_coiterator Lambda BS)) (bs_transition BS x))).
Proof.
 apply (commutativity_Fib_fst_snd Lambda BS x).
Defined.

Lemma commutativity_Fib_Cons_1 (Lambda:T_over_B_distributive) (BS: BT_coalgebroid) (x:BS.(bs_states)) : 
 Lam_coiterator Lambda BS x (=) Cons (fst (lift_B_ _ _ (Beta Lambda) (lift_B_ _ _  (lift_T_ _ _ (Lam_coiterator Lambda BS)) (bs_transition BS x))))
                           (snd (lift_B_ _ _ (Beta Lambda) (lift_B_ _ _  (lift_T_ _ _ (Lam_coiterator Lambda BS)) (bs_transition BS x)))).
Proof.
 rewrite (hd_tl_id (Lam_coiterator Lambda BS x)).
 destruct (commutativity_Fib_hd_tl Lambda BS x) as [hyp_hd hyp_tl].
 constructor.
  rewrite hyp_hd; reflexivity.
  unfold tl at 1.
  match goal with 
  | [ id1 : ?X1 (=) ?X2  |- _ ] => apply trans_bisimilar with X2; trivial
  end.
  apply refl_bisimilar. 
Defined.

Section Example_fibonacci.

(** Example:

<<
fib = 0 :: plus_tl 1 fib fib

plus_tl x0 (x:xs) (y:ys) = x0+y :: plus_tl x xs ys
>>

*)

Open Scope Z_scope.


Definition lambda_fibonacci (X:Set) (sbx:T_ (B_ X)) : B_ (T_ X) :=
       let (b0, t0) := sbx in let (t1, t2) := t0 in let (b1, x1) := t1 in let (b2, x2) := t2 in 
        (b0+b2, (b1, (x1, x2))).

Lemma lambda_fibonacci_natural: forall (X Y : Set) (f : X -> Y) (sbx : T_ (B_ X)),
    lambda_fibonacci Y (lift_T_ (B_ X) (B_ Y) (lift_B_ X Y f) sbx) =  lift_B_ (T_ X) (T_ Y) (lift_T_ X Y f) (lambda_fibonacci X sbx).
Proof.
 intros X Y f [b0 [[b1 x1] [b2 x2]]]; trivial. 
Defined.
 
Definition Lambda_fibonacci:T_over_B_distributive := Build_T_over_B_distributive lambda_fibonacci lambda_fibonacci_natural.

Definition coalgebra_fibonacci: BT_coalgebroid := Build_BT_coalgebroid unit (fun t : unit => (0,(1,(tt,tt)))).

Definition fib:=Lam_coiterator Lambda_fibonacci coalgebra_fibonacci tt.

Definition pointwise_plus_tl x xs ys := Beta Lambda_fibonacci (x,(xs,ys)).

(*
Time Eval vm_compute in (take 20 fib).
*)

Lemma pointwise_plus_tl_cofixed :forall x xs ys, pointwise_plus_tl x xs ys = 
                               Cons (x+(hd ys)) (pointwise_plus_tl (hd xs) (tl xs) (tl ys)).
Proof.
 intros x xs ys.
 unfold pointwise_plus_tl, Beta, Lambda_fibonacci, F_unfold.
 simpl; rewrite Str_unfold_unfolded.
 reflexivity.
Defined.

Lemma fib_cofixed : fib (=)  Cons 0 (pointwise_plus_tl 1 fib fib).
Proof.
 assert (hyp_bis:=commutativity_Fib_Cons_1 Lambda_fibonacci coalgebra_fibonacci tt);
 match goal with 
 | [ id1 : ?X1 (=) ?X2  |- _ ] => apply trans_bisimilar with X2
 end; 
 [ assumption
 | apply refl_bisimilar
 ].
Defined.

Section fib_satisfies_other_equation.  

(* Proving an alternative bisimilarity for fib in two different ways. *)

Section using_cofix.

Lemma pointwise_plus_pointwise_plus_tl :forall x xs ys, pointwise_plus_tl x xs ys (=) pointwise_plus (Cons x xs) ys.
Proof.
 cofix.
 destruct xs as [x0 xs], ys as [y0 ys].
 rewrite (pointwise_plus_tl_cofixed x (Cons x0 xs) (Cons y0 ys)).
 rewrite pointwise_plus_cofixed.
 constructor; trivial.
  apply (pointwise_plus_pointwise_plus_tl x0 xs ys).
Defined.

Lemma pointwise_plus_comm :forall xs ys, pointwise_plus xs ys (=) pointwise_plus ys xs.
Proof.
 cofix.
 destruct xs as [x0 xs], ys as [y0 ys].
 rewrite pointwise_plus_cofixed.
 replace (pointwise_plus (Cons y0 ys) (Cons x0 xs)) with (Cons (y0 + x0) (pointwise_plus ys xs)); [|symmetry ; apply pointwise_plus_cofixed].
 constructor; simpl.
  auto with zarith. 
  apply pointwise_plus_comm. 
Defined.

Lemma fib_satisfies_other_equation : fib (=)  Cons 0 (Cons 1 (pointwise_plus (tl fib) fib)).
Proof.
 apply trans_bisimilar with (Cons 0 (pointwise_plus_tl 1 fib fib));[apply fib_cofixed|].
 constructor; trivial.
 apply trans_bisimilar with (pointwise_plus (Cons 1 fib) fib); [apply (pointwise_plus_pointwise_plus_tl 1 fib fib)|].
 rewrite pointwise_plus_cofixed.
 constructor; [trivial|simpl; apply pointwise_plus_comm].
Defined.

End using_cofix.

Section without_cofix.

Definition gamma_pointwise_plus_pointwise_plus_tl:
  let R':=fun xs ys => exists x0, exists xs0, exists ys0, xs = pointwise_plus_tl x0 xs0 ys0 /\ ys = pointwise_plus (Cons x0 xs0) ys0 in 
              {s1s2 : states w * states w &  R' (fst s1s2) (snd s1s2)} ->
              Streams_as_Weakly_Final_Coalgebra.F_ {s1s2 : states w * states w &  R' (fst s1s2) (snd s1s2)}.
Proof.
 intros R' [[s1 s2] hypR'].
  simpl in hypR'.
  assert (hyp_tl:R' (tl s1) (tl s2)). 
   destruct hypR' as (x & xs & ys & hyp1 & hyp2).
   subst R'; exists (hd xs); exists (tl xs); exists (tl ys).
   rewrite hyp1, hyp2, pointwise_plus_tl_cofixed, pointwise_plus_cofixed; split; simpl; trivial.
   rewrite <- hd_tl_id; trivial.
   refine (hd s1,_); exists (tl s1,tl s2); assumption.
Defined.

Lemma pointwise_plus_pointwise_plus_tl_2 :forall x xs ys, pointwise_plus_tl x xs ys (=) pointwise_plus (Cons x xs) ys.
Proof.
 intros x xs ys.
 destruct (maximal_bisimulation_is_maximal w w) as [_ hyp].
 set (R':=fun alpha beta => exists x, exists xs, exists ys, alpha = pointwise_plus_tl x xs ys /\ beta = pointwise_plus (Cons x xs) ys).  
 apply (hyp R').
 assert (R'_bis:is_F_bisimulation_strong w w R') ;[|exists R'_bis; trivial].
  clear; exists (gamma_pointwise_plus_pointwise_plus_tl).
  intros [[xs ys] hyp]; split; simpl; trivial; f_equal.
  destruct hyp as (x0 & xs0 & ys0 & hyp1 & hyp2).
  simpl in hyp1,hyp2; rewrite hyp1, hyp2, pointwise_plus_cofixed, pointwise_plus_tl_cofixed; trivial.
 exists x; exists xs;exists ys; split; trivial. 
Defined.

Definition gamma_pointwise_plus_comm:
  let R':=fun xs ys => exists xs0, exists ys0, xs = pointwise_plus xs0 ys0 /\ ys = pointwise_plus ys0 xs0 in 
              {s1s2 : states w * states w &  R' (fst s1s2) (snd s1s2)} ->
              Streams_as_Weakly_Final_Coalgebra.F_ {s1s2 : states w * states w &  R' (fst s1s2) (snd s1s2)}.
Proof.
 intros R' [[s1 s2] hypR'].
  simpl in hypR'.
  assert (hyp_tl:R' (tl s1) (tl s2)). 
   destruct hypR' as (xs & ys & hyp1 & hyp2).
   subst R'; exists (tl xs); exists (tl ys).
   rewrite hyp1, hyp2, pointwise_plus_cofixed; split; simpl; trivial.
   refine (hd s1,_); exists (tl s1,tl s2); assumption.
Defined.

Lemma pointwise_plus_comm_2 :forall xs ys, pointwise_plus xs ys (=) pointwise_plus ys xs.
Proof.
 intros xs ys.
 destruct (maximal_bisimulation_is_maximal w w) as [_ hyp].
 set (R':=fun alpha beta => exists xs, exists ys, alpha = pointwise_plus xs ys /\ beta = pointwise_plus ys xs).  
 apply (hyp R').
 assert (R'_bis:is_F_bisimulation_strong w w R') ;[|exists R'_bis; trivial].
  clear; exists (gamma_pointwise_plus_comm).
  intros [[xs ys] hyp]; split; simpl; trivial; f_equal.
  destruct hyp as (xs0 & ys0 & hyp1 & hyp2).
  simpl in hyp1,hyp2; rewrite hyp1, hyp2, pointwise_plus_cofixed; simpl; auto with zarith. 
 exists xs;exists ys; split; trivial. 
Defined.

Lemma fib_satisfies_other_equation_2 : fib (=)  Cons 0 (Cons 1 (pointwise_plus (tl fib) fib)).
Proof.
 apply trans_bisimilar with (Cons 0 (pointwise_plus_tl 1 fib fib));[apply fib_cofixed|].
 constructor; trivial.
 apply trans_bisimilar with (pointwise_plus (Cons 1 fib) fib); [apply (pointwise_plus_pointwise_plus_tl_2 1 fib fib)|].
 rewrite pointwise_plus_cofixed.
 constructor; [trivial|simpl; apply pointwise_plus_comm_2].
Defined.

End without_cofix.

End fib_satisfies_other_equation.

End Example_fibonacci.



Module Import primitive_corecursion_Zstreams:= Primitive_Corecursion Streams_as_Weakly_Final_Coalgebra.

Import Corecursion_LamCoiter.

Lemma commutativity_Primitive_Corecursion_fst_snd (BT: BT_coalgebroid) (x:BT.(bs_states)) : 
 fst (Str.(transition) (Corecursor BT x)) =
 fst (lift_B_ _ _ (prim_corec_tupling _ (Corecursor BT)) (BT.(bs_transition) x)) /\
 snd (Str.(transition) (Corecursor BT x)) (=) 
 snd (lift_B_ _ _ (prim_corec_tupling _ (Corecursor BT)) (BT.(bs_transition) x)).
Proof.
 apply -> rel_image_lift_F_Str_bisimilar_spelled.
 apply commutativity_Corecursor_rel_image_lifting.
Defined.

Lemma commutativity_Primitive_Corecursion_hd_tl (BT: BT_coalgebroid) (x:BT.(bs_states)) : 
 hd (Corecursor BT x) =
 fst (lift_B_ _ _ (prim_corec_tupling _ (Corecursor BT)) (BT.(bs_transition) x)) /\
 tl (Corecursor BT x) (=) 
 snd (lift_B_ _ _ (prim_corec_tupling _ (Corecursor BT)) (BT.(bs_transition) x)).
Proof.
 apply (commutativity_Primitive_Corecursion_fst_snd BT x).
Defined.

Lemma commutativity_Primitive_Corecursion_Cons (BT: BT_coalgebroid) (x:BT.(bs_states)) : 
 Corecursor BT x (=) Cons (fst (lift_B_ _ _ (prim_corec_tupling _ (Corecursor BT)) (BT.(bs_transition) x)))
                          (snd (lift_B_ _ _ (prim_corec_tupling _ (Corecursor BT)) (BT.(bs_transition) x))).
Proof.
 rewrite (hd_tl_id (Corecursor BT x)).
 destruct (commutativity_Primitive_Corecursion_hd_tl BT x) as [hyp_hd hyp_tl].
 constructor.
  rewrite hyp_hd; reflexivity.
  unfold tl at 1.
  match goal with 
  | [ id1 : ?X1 (=) ?X2  |- _ ] => apply trans_bisimilar with X2; trivial
  end.
  apply refl_bisimilar. 
Defined.

Section primitive_corecursion_example.

Section insert.

Definition coalgebra_insert: BT_coalgebroid := 
    (Build_BT_coalgebroid (B*B_pow_inf)
         (fun  pivot_xs: B * B_pow_inf =>
          match pivot_xs with
          | (pivot, Cons x0 xs' as xs) =>
              if Z_le_dec x0 pivot
              then (x0, il (B * Stream B) (pivot, xs'))
              else (pivot, ir (B * B_pow_inf) xs)
          end)).


Definition insert x ys:=Corecursor coalgebra_insert (x,ys).

Lemma insert_cofixed :forall x ys, insert x ys (=) 
                      if Z_le_dec (hd ys) x
                      then Cons (hd ys) (insert x (tl ys)) 
                      else Cons x ys.
Proof.
 intros x ys;
 assert (hyp_bis:=commutativity_Primitive_Corecursion_Cons coalgebra_insert (x,ys));
 match goal with 
 | [ id1 : ?X1 (=) ?X2  |- _ ] => apply trans_bisimilar with X2
 end; 
 [ assumption
 | destruct ys as [y ys']; simpl; destruct (Z_le_dec y x); apply refl_bisimilar 
 ].
Qed. 

End insert.

End primitive_corecursion_example.