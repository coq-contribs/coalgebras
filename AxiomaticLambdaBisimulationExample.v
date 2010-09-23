(************************************************************************)
(* Copyright 2010 Milad Niqui                                           *)
(* This file is distributed under the terms of the                      *)
(* GNU Lesser General Public License Version 3                          *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses/lgpl-3.0.html>         *)
(************************************************************************)

(* WARNING: 

This files presents a development based on an axiom. This is NOT a
module axiom that can be instantiated, so using the results in this
file may propagate this axiom.

*)


Require Import LambdaCoiterationExamples.
Require Import IntensionalLambdaBisimulation.
Require Import ZStreamCoalgebra.

Module Streams_Conv_LamBisim := Lambda_Bisimulation_theory Streams_as_Weakly_Final_Coalgebra Pairing_Functor.
Import Streams_Conv_LamCoiter.


Axiom bisimilar_is_equal_Streams: forall xs ys, xs (=) ys -> xs = ys.

Section lambda_bisimulation_example.

Definition gamma_shuffle_product_comm:
  let R':=fun xs ys => { xs0: w.(states) & { ys0 : w.(states) | 
                        xs = shuffle_product xs0 ys0 /\ ys = shuffle_product ys0 xs0}} in 
              {s1s2 : states w * states w &  R' (fst s1s2) (snd s1s2)} ->
              Streams_Conv_LamCoiter.B_ (Streams_Conv_LamCoiter.T_ 
                      {s1s2 : states w * states w & R' (fst s1s2) (snd s1s2)}).
Proof.
 intros R' [[s1 s2] [alpha [beta [hypR'_l hypR'_r]]]].
 simpl in hypR'_l, hypR'_r.
 assert (hyp_tl1:R' (shuffle_product (tl alpha) beta) (shuffle_product beta (tl alpha))).
  subst R'; exists (tl alpha); exists beta; tauto.
 assert (hyp_tl2:R' (shuffle_product alpha (tl beta)) (shuffle_product (tl beta)  alpha)).
  subst R'; exists alpha; exists (tl beta); tauto.
 assert (hyp_tl3:R' (shuffle_product beta (tl alpha)) (shuffle_product (tl alpha) beta)).
  subst R'; exists beta; exists (tl alpha); tauto.
 assert (hyp_tl4:R' (shuffle_product (tl beta) alpha) (shuffle_product alpha (tl beta))).
  subst R'; exists (tl beta); exists alpha; tauto.
 refine (hd s1,_).
 refine (_,_).
 exists ((shuffle_product (tl alpha) beta),(shuffle_product beta (tl alpha))); assumption.
 exists ((shuffle_product alpha (tl beta)),(shuffle_product (tl beta) alpha)); assumption.
Defined.


Lemma shuffle_product_comm: forall xs ys, shuffle_product xs ys (=) shuffle_product ys xs.
Proof.
 intros xs ys.
 set (R:=fun xs ys => { xs0: w.(states) & { ys0 : w.(states) | 
                        xs = shuffle_product xs0 ys0 /\ ys = shuffle_product ys0 xs0}}).
 apply (lambda_coinduction_strong Lambda_convolution R).
  subst R; simpl. 
  exists xs; exists ys; split; auto. 
 clear; exists gamma_shuffle_product_comm.
  intros [[s1 s2] [alpha [beta [hyp_l hyp_r]]]].
  simpl in hyp_l, hyp_r, s1, s2.
  split.
   stepl (hd s1, (pointwise_plus (shuffle_product (tl alpha) beta) (shuffle_product alpha (tl beta)))); trivial;
   simpl; f_equal; subst s1.
   apply bisimilar_is_equal_Streams.   (* ### AXIOM ### *) 
   rewrite (shuffle_product_cofixed alpha beta); apply refl_bisimilar.

   stepl (hd s1, (pointwise_plus (shuffle_product beta (tl alpha))) (shuffle_product (tl beta) alpha)).
 
    simpl; f_equal; subst s2.
     subst s1; rewrite shuffle_product_cofixed; rewrite (shuffle_product_cofixed beta alpha); simpl; auto with zarith.
     apply bisimilar_is_equal_Streams.   (* ### AXIOM ### *) 
     rewrite (shuffle_product_cofixed beta alpha); apply pointwise_plus_comm.

  simpl; f_equal.
Qed.

End lambda_bisimulation_example.
