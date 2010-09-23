(************************************************************************)
(* Copyright 2008-2010 Milad Niqui                                      *)
(* This file is distributed under the terms of the                      *)
(* GNU Lesser General Public License Version 3                          *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses/lgpl-3.0.html>         *)
(************************************************************************)

Require Export Bisimulation.

(** Module type for weakly final coalgebras. *)

Module Type Weakly_Final_Coalgebra.

Include Bisimulation_For_Coalgebra.

Definition is_weakly_final (w:F_coalgebra) := forall (S0:F_coalgebra),
   { F_unfold_ : S0.(states) -> w.(states) | 
     forall s0, w.(transition) (F_unfold_ s0) = lift_F_ _ _ F_unfold_ (S0.(transition) s0)}.

Parameter w:F_coalgebra.

Axiom w_is_weakly_final:is_weakly_final w.

Definition F_unfold (S0:F_coalgebra) := proj1_sig (w_is_weakly_final S0).

Definition commutativity_F_unfold (S0:F_coalgebra) :forall (x:S0.(states)), w.(transition) (F_unfold S0 x) = (lift_F_ _ _ (F_unfold S0)) (S0.(transition) x) := proj2_sig (w_is_weakly_final S0).

Definition bisimilar := maximal_bisimulation w w.

Notation " A (=) B " := (bisimilar A B) (at level 70).

Axiom F_unique:forall (S0:F_coalgebra) f g, 
   (forall (s0: S0.(states)), w.(transition) (f s0) = (lift_F_ _ _ f) (S0.(transition) s0) ) ->
   (forall (s0: S0.(states)), w.(transition) (g s0) = (lift_F_ _ _ g) (S0.(transition) s0) ) ->
   forall s, f s(=) g s.

Axiom lift_F_extensionality_bisim: forall (X:Set) (f0 f1:X->w.(states)) fx, (forall x, f0 x (=) f1 x) -> rel_image_lift_F_ _ _ bisimilar (lift_F_  _ _ f0 fx) (lift_F_ _ _ f1 fx).


End Weakly_Final_Coalgebra.


Module Weakly_Final_Coalgebra_theory (MB:Weakly_Final_Coalgebra).

Import MB.
Export MB.

Include (Bisimulation_theory MB).


Lemma ordinary_coinduction:forall (R: w.(states)-> w.(states)->Prop) x y, 
    R x y-> is_F_bisimulation _ _ R -> x (=) y.
Proof.
 intros R x y hyp_R hyp_bisim; apply bisimulation_maximal_bisimulation with R; trivial.
Qed.  

Lemma strong_ordinary_coinduction:forall  (R: w.(states)-> w.(states)->Set) x y, 
    R x y-> is_F_bisimulation_strong _ _ R -> x (=) y.
Proof.
 intros R x y hyp_R hyp_bisim; apply bisimulation_strong_maximal_bisimulation with R; trivial.
Qed.

Lemma F_unfold_injectve (S0 : F_coalgebra) x y : x = y -> (F_unfold S0) x = (F_unfold S0) y.
Proof.
 intros hyp1; subst x; reflexivity.
Qed.

Lemma F_unfold_bisim_congruence (S0:F_coalgebra) R x y : (is_F_bisimulation S0 S0 R) -> R x y -> (F_unfold S0) x (=) (F_unfold S0) y.
Proof.
 intros [gamma hyp_gamma] hyp1.
 change (  (fun s1s2 => F_unfold S0 (fst (proj1_sig s1s2))) (exist (fun s1s2=> R (fst s1s2) (snd s1s2)) (x,y) hyp1) (=)
           (fun s1s2 => F_unfold S0 (snd (proj1_sig s1s2))) (exist (fun s1s2=> R (fst s1s2) (snd s1s2)) (x,y) hyp1)   ).
 apply (F_unique (Build_F_coalgebra {s1s2 : states S0 * states S0 | R (fst s1s2) (snd s1s2)} gamma));
 intros s1s2hyp; destruct (hyp_gamma s1s2hyp) as [H1 H2];
 [ rewrite (commutativity_F_unfold S0 (fst (proj1_sig s1s2hyp))); rewrite <- H1
 | rewrite (commutativity_F_unfold S0 (snd (proj1_sig s1s2hyp))); rewrite <- H2]
 ; rewrite lift_F_compose; apply lift_F_extensionality; trivial.
Qed.

Lemma F_unfold_morphism (S0:F_coalgebra) x y : (maximal_bisimulation S0 S0) x y -> (F_unfold S0) x (=) (F_unfold S0) y.
Proof.
 intros hyp1;
 apply (F_unfold_bisim_congruence _ (maximal_bisimulation S0 S0)); trivial;
 apply maximal_bisimulation_is_bisimulation.
Qed.

Lemma F_unfold_morphism_inversion (S0:F_coalgebra) x y : (F_unfold S0) x (=) (F_unfold S0) y -> (maximal_bisimulation S0 S0) x y.
Proof.
 intros hyp1.
 set (f:=F_unfold S0).
 set (f_inv_delta:=fun x y=> f x (=) f y).
 apply bisimulation_maximal_bisimulation with f_inv_delta.
  assumption.
  apply inverse_image_F_bisimulation_is_F_bisimulation.
   subst f; intros s0; symmetry; apply (commutativity_F_unfold S0 s0).
   apply maximal_bisimulation_is_bisimulation.
Qed.

Add Parametric Morphism (S0:F_coalgebra) : (F_unfold S0) 
 with signature  (maximal_bisimulation S0 S0) ==> (maximal_bisimulation w w) as F_unfold_Morphism.
Proof. 
 apply F_unfold_morphism.
Qed.

Definition coconstructor : F_ w.(states) -> w.(states) := F_unfold (Build_F_coalgebra (F_ w.(states)) (lift_F_ _ _ w.(transition))).

Lemma coconstructor_destructor: forall x, coconstructor (w.(transition) x) (=) x.
Proof.
 intros x.
 generalize (commutativity_F_unfold (Build_F_coalgebra (F_ w.(states)) (lift_F_ _ _ w.(transition)))).
 simpl in *; fold coconstructor. 
 intros hyp_cocon.
 apply (F_unique w (fun x=>coconstructor (w.(transition) x)) (fun x=>x)); intros x0.
  rewrite (hyp_cocon (w.(transition) x0)); rewrite lift_F_compose; trivial.
  apply lift_F_id.
Qed.

Lemma destructor_equal_inversion: forall x1 x2, w.(transition) x1 = w.(transition) x2 -> x1 (=) x2.
Proof.
 intros x1 x2 hyp1.
 rewrite <- (coconstructor_destructor x1). 
 rewrite <- (coconstructor_destructor x2). 
 apply F_unfold_morphism.
 rewrite hyp1.
 apply refl_bisimilar.
Qed.

Lemma destructor_maximum_bisimulation_inversion: forall x1 x2, 
   maximal_bisimulation (Build_F_coalgebra (F_ w.(states)) (lift_F_ _ _ w.(transition))) 
                        (Build_F_coalgebra (F_ w.(states)) (lift_F_ _ _ w.(transition))) (w.(transition) x1) (w.(transition) x2) -> 
     x1 (=) x2.
Proof.
 intros x1 x2 hyp1.
 rewrite <- (coconstructor_destructor x1). 
 rewrite <- (coconstructor_destructor x2). 
 apply F_unfold_morphism; assumption.
Qed.

Lemma destructor_morphism : forall x y, x(=)y ->
   maximal_bisimulation (Build_F_coalgebra (F_ w.(states)) (lift_F_ _ _ w.(transition))) 
                        (Build_F_coalgebra (F_ w.(states)) (lift_F_ _ _ w.(transition))) 
                        (w.(transition) x) (w.(transition) y).
Proof.
 intros x y hyp.
 apply F_unfold_morphism_inversion.
 fold coconstructor.
 do 2 rewrite coconstructor_destructor; trivial.
Qed. 

Lemma rel_image_maximal_bisimulation_inversion: forall fw1 fw2,
                        rel_image_lift_F_ _ _ bisimilar fw1 fw2 ->
   maximal_bisimulation (Build_F_coalgebra (F_ w.(states)) (lift_F_ _ _ w.(transition))) 
                        (Build_F_coalgebra (F_ w.(states)) (lift_F_ _ _ w.(transition))) fw1 fw2.
Proof.
 intros fw1 fw2 (x & y & hyp1 & hyp2 & hyp3).
 subst fw1 fw2; trivial; apply destructor_morphism; trivial.
Qed.


Add Morphism w.(transition)
 with signature  (maximal_bisimulation w w) ==> 
                 (maximal_bisimulation (Build_F_coalgebra (F_ w.(states)) (lift_F_ _ _ w.(transition)))
                                       (Build_F_coalgebra (F_ w.(states)) (lift_F_ _ _ w.(transition)))) 
   as destructor_Morphism.
Proof. 
 apply destructor_morphism.
Qed.

Lemma rel_image_bisimilar_transitive: forall fw1 fw2 fw3,
                        rel_image_lift_F_ _ _ bisimilar fw1 fw2 ->
                        rel_image_lift_F_ _ _ bisimilar fw2 fw3 ->
                        rel_image_lift_F_ _ _ bisimilar fw1 fw3.
Proof.
 intros fs1 fs2 fs3 (x1 & y1 & hyp11 & hyp12 & hyp13) (x2 & y2 & hyp21 & hyp22 & hyp23).
 red.
 exists x1; exists y2.
 repeat split; trivial.
 rewrite hyp11. 
 rewrite <- hyp21.
 symmetry.
 apply destructor_equal_inversion.
 rewrite <- hyp13.
 rewrite <- hyp22; trivial.
Qed.

End Weakly_Final_Coalgebra_theory.