(************************************************************************)
(* Copyright 2010 Milad Niqui                                           *)
(* This file is distributed under the terms of the                      *)
(* GNU Lesser General Public License Version 3                          *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses/lgpl-3.0.html>         *)
(************************************************************************)

(** Formalisation of the Lambda-bisimulation and Lambda-coinduction
using intensional commutativity of diagrams. The original definitions come from [1].

[1] Falk Bartels. On Generalised Coinduction and Probabilistic specification Formats:
   Distributive laws in coalgebraic modelling. PhD thesis, VU Amsterdam, 2004.

*)


Require Export LambdaCoiteration.

Module Lambda_Bisimulation_theory (MB:Weakly_Final_Coalgebra) (MT:Set_Functor).

Include (Lambda_Coiteration_theory MB MT).

Record TB_bialgebra : Type :=
{ coalgebra_part : B_coalgebra
; algebra_part : F_ coalgebra_part.(states) -> coalgebra_part.(states)
}.

Record F_algebra : Type :=
{ carrier : Set
; operation : F_ carrier -> carrier
}.

Definition is_lambda_bialgebra (Lambda:T_over_B_distributive) (Xtb:TB_bialgebra):=
       let alpha_X:=transition Xtb.(coalgebra_part) in
       let beta_X:=Xtb.(algebra_part) in
       forall  (tx:T_ (states Xtb.(coalgebra_part))), lift_B_ _ _ beta_X (Lambda.(lambda_) _ (lift_T_ _ _ alpha_X tx)) = alpha_X (beta_X tx).

Fixpoint iterate_algebra (j:nat) (X:F_algebra) {struct j} : T_iter j X.(carrier) -> X.(carrier):=
         match j with
         | O => fun tx => tx
         | S j' => fun tx => iterate_algebra j' X (lift_T_iter _ _ X.(operation) j' tx)
         end.


Definition Beta_iter (j:nat) (X:TB_bialgebra) : T_iter j (states X.(coalgebra_part)) ->states X.(coalgebra_part):=
   iterate_algebra j (Build_F_algebra (states X.(coalgebra_part)) X.(algebra_part)).

Definition star_algebra (X:F_algebra) := infinite_case_analysis _ _ (fun j=>iterate_algebra j X).

Definition Beta_star (X:TB_bialgebra) := star_algebra (Build_F_algebra (states X.(coalgebra_part)) X.(algebra_part)).

Theorem lambda_iter_naturality: forall (Lambda : T_over_B_distributive) (j:nat) (X Y : Set) (f : X -> Y)
     (tjbx : T_iter j (B_ X)),
   lift_B_ _ _ (lift_T_iter X Y f j) (lambda_iter_ Lambda j X tjbx) =
   lambda_iter_ Lambda j Y (lift_T_iter (B_ X) (B_ Y) (lift_B_ X Y f) j tjbx).
Proof.
 intros [lam_ nat_lam_] j; induction j; intros X Y f tjbx; trivial.
  fold T_iter in IHj.
 
  change ( lift_B_ _ _ (lift_T_iter _ _ (lift_F_ X Y f) j) (lambda_iter_ (Build_T_over_B_distributive lam_ nat_lam_) j (T_ X) 
                (lift_T_iter _ _ (lam_ X) j tjbx)) =
          lambda_iter_ (Build_T_over_B_distributive lam_ nat_lam_) j (T_ Y)
     (lift_T_iter _ _ (lam_ Y) j
       (lift_T_iter _ _ (lift_B_ X Y f) (S j) tjbx) )); trivial.
  rewrite (IHj (T_ X) (T_ Y) (lift_T_ _ _ f)).
  f_equal.
  simpl.
  do 2 rewrite lift_T_iter_compose.
  fold lift_T_iter T_ B_.
  apply lift_T_iter_extensionality.
  symmetry; apply nat_lam_.
Qed.

Lemma lambda_star_naturality: forall (Lambda : T_over_B_distributive) (X Y : Set) 
     (f : X -> Y) (tsbx : T_star_ (B_ X)),
   lift_B_ (T_star_ X) (T_star_ Y) (lift_T_star_ X Y f)
     (lambda_star Lambda X tsbx) =
   lambda_star Lambda Y
     (lift_T_star_ (B_ X) (B_ Y) (lift_B_ X Y f) tsbx).
Proof.
 intros Lambda X Y f [j tjbx].
 unfold lambda_star at 1.
 fold B_.
 simpl.

 set (tmp:=lambda_iter_ Lambda j X tjbx).
 stepl (lift_B_ _ _ (T_star_coproject_ Y j) (lift_B_ _ _ (lift_T_iter _ _ f j) tmp));
 [|do 2 rewrite lift_B_compose; apply lift_B_extensionality; trivial].
 subst tmp.
 f_equal.
 fold T_iter. 
 apply lambda_iter_naturality.
Qed.

Lemma Lam_bisimulation_4_1_5_lambda_star_iterate : forall (Lambda:T_over_B_distributive) (j:nat) (Xtb:F_algebra)
   (tjbx : T_iter j (B_ Xtb.(carrier))),
   iterate_algebra j (Build_F_algebra _ (fun tbx=> lift_B_ _ _ Xtb.(operation) (Lambda.(lambda_) _ tbx))) tjbx =
   lift_B_ _ _ (fun x => iterate_algebra j Xtb x) (lambda_iter_ Lambda j _ tjbx).
Proof.
 intros [lam_ lam_nat_] j; induction j; intros [X beta_X] tjbx; unfold carrier, operation.
  (* O *)
  apply lift_B_id.
  
  (* S j*)
  simpl.
  fold T_.
  set (tmp:=lift_T_iter (T_ (B_ X)) (B_ X) (fun tbx => lift_B_ (T_ X) X beta_X (lam_ X tbx)) j tjbx).
  (* triangle1, IH *)
  assert (hyp_rewrite_tmp:=IHj (Build_F_algebra X beta_X) tmp).
  fold T_ in hyp_rewrite_tmp.
  simpl in hyp_rewrite_tmp.
  rewrite hyp_rewrite_tmp; clear hyp_rewrite_tmp.

  (* triangle2 *)
  rewrite <- (lift_B_compose (T_iter j (T_ X)) (T_iter j X) X); fold lift_B_.

  assert (left_commut:lambda_iter_ (Build_T_over_B_distributive lam_ lam_nat_) j X tmp=
          lift_B_ (T_iter j (T_ X)) (T_iter j X) (lift_T_iter (T_ X) X beta_X j)
        (lambda_iter_ (Build_T_over_B_distributive lam_ lam_nat_) j 
           (T_ X) (lift_T_iter (T_ (B_ X)) (B_ (T_ X)) (lam_ X) j tjbx))); [|rewrite left_commut; apply lift_B_extensionality; trivial].
  subst tmp.
  rewrite <- (lift_T_iter_compose (T_ (B_ X)) (B_ (T_ X))); fold lift_T_iter.
  set (tmp2:=lift_T_iter (T_ (B_ X)) (B_ (T_ X)) (lam_ X) j tjbx).
  symmetry.
  apply lambda_iter_naturality.
Qed.

Lemma Lam_bisimulation_4_1_5_lambda_star_universality : forall (Lambda:T_over_B_distributive) (Xtb:F_algebra)
     (hbx:T_star_ (B_ Xtb.(carrier))),
    star_algebra (Build_F_algebra (B_ Xtb.(carrier)) (fun tbx => lift_B_ _ _ Xtb.(operation) (Lambda.(lambda_) _ tbx))) hbx =
    lift_B_ _ _ (star_algebra Xtb) (lambda_star Lambda _ hbx). 
Proof.
 intros Lambda Xtb [j tjbx].
 simpl.
 rewrite lift_B_compose; fold lift_B_.
 unfold star_algebra.
 simpl.
 apply (Lam_bisimulation_4_1_5_lambda_star_iterate Lambda j Xtb tjbx).
Qed.

Lemma Lam_bisimulation_4_1_5_iterate_pres_algebra_morphism :forall (j:nat) (Xa Ya:F_algebra) (f: Xa.(carrier) -> Ya.(carrier)),
   (forall tx, Ya.(operation) (lift_T_ _ _ f tx) = f (Xa.(operation) tx)) -> 
   forall tjx, iterate_algebra j Ya (lift_T_iter _ _ f j tjx) = f (iterate_algebra j Xa tjx).
Proof.
 induction j; intros [X beta_X] [Y beta_Y] f hyp_alg_map tjx; simpl in *; trivial.
 
 rewrite <- (IHj (Build_F_algebra X beta_X) (Build_F_algebra Y beta_Y) f hyp_alg_map).
 rewrite lift_T_iter_compose; fold lift_T_iter; simpl.
 f_equal.
 rewrite lift_T_iter_compose; fold lift_T_iter; simpl.
 apply lift_T_iter_extensionality.
 assumption.
Qed.

Lemma Lam_bisimulation_4_1_5_star_pres_algebra_morphism :forall (Xa Ya:F_algebra) (f: Xa.(carrier) -> Ya.(carrier)),
    (forall tx, Ya.(operation) (lift_T_ _ _ f tx) = f (Xa.(operation) tx)) ->
    (forall hx, (star_algebra Ya) (lift_T_star_ _ _ f hx) = f ((star_algebra Xa) hx)).
Proof.
 intros Xa Ya f hyp_alg_map [j tjx].
 unfold star_algebra.
 simpl in *.
 apply (Lam_bisimulation_4_1_5_iterate_pres_algebra_morphism j); trivial.
Qed.

Lemma Lam_bisimulation_4_1_5_lambda_star_bialgebra : forall (Lambda:T_over_B_distributive) (Xtb:TB_bialgebra)
     (hx:T_star_ (states Xtb.(coalgebra_part))),
   is_lambda_bialgebra Lambda Xtb ->
   lift_B_ _ _ (Beta_star Xtb) (lambda_star Lambda _ (lift_T_star_ _ _ (transition Xtb.(coalgebra_part)) hx)) = transition Xtb.(coalgebra_part) (Beta_star Xtb hx).
Proof.  
 intros Lambda [[X alpha_X] beta_X] hx hyp_lam_bialg.
 unfold Beta_star; simpl in *.
 set (tmp:=lift_T_star_ X (MB.F_ X) alpha_X hx).
 rewrite <- (Lam_bisimulation_4_1_5_lambda_star_universality Lambda (Build_F_algebra X beta_X)).
 simpl.
 subst tmp.
 rewrite (Lam_bisimulation_4_1_5_star_pres_algebra_morphism (Build_F_algebra X beta_X) 
                 (Build_F_algebra _ (fun tbx=>lift_B_ _ _ beta_X (lambda_ Lambda X tbx)))
                  alpha_X); trivial.
Qed.
 

Definition is_like_lambda_bismulation (X:BT_coalgebroid) (Y:TB_bialgebra) 
              (f:X.(bs_states)->states Y.(coalgebra_part)) (x:X.(bs_states)) :=
  lift_B_ _ _ (fun fr=>Y.(algebra_part) (lift_T_ _ _  f fr)) (X.(bs_transition) x) =
  transition (Y.(coalgebra_part)) (f x).

Lemma is_like_lambda_bismulation_T_star_span_bisimulation (Lambda:T_over_B_distributive)
 (X:BT_coalgebroid) (Y:TB_bialgebra)
 (pi:X.(bs_states)->states Y.(coalgebra_part)) 
 (hyp_lam_bisim:forall (r:X.(bs_states)), is_like_lambda_bismulation X Y pi r)
 (hr: T_star_ X.(bs_states)) :
   let P:=states Y.(coalgebra_part) in
   let alpha_P:=transition Y.(coalgebra_part) in
   let beta_P:=Y.(algebra_part) in
   let R:=X.(bs_states) in
    let gamma := X.(bs_transition) in
       let T_star_gamma := lift_T_star_ _ _ gamma in
         let lambda_star_TR := lambda_star Lambda (T_ R) in
           let B_Chi_R := lift_B_ _ _ (Chi R) in
             let alpha_gamma := fun hr0 => B_Chi_R (lambda_star_TR (T_star_gamma hr0)) in
               is_lambda_bialgebra Lambda Y ->
                lift_B_ _ _ (fun hr0=>Beta_star Y (lift_T_star_ _ _ pi hr0)) (alpha_gamma hr) =
                alpha_P (Beta_star Y (lift_T_star_ _ _ pi hr)). 
Proof.
 intros P alpha_P beta_P R gamma T_star_gamma lambda_star_TR B_Chi_R alpha_gamma hyp_lam_bialg.
 red in hyp_lam_bisim.
 fold P R lift_B_.
 rewrite <- (lift_B_compose _ _ _ (lift_T_star_ R P pi) (Beta_star Y)).
 fold B_; fold lift_B_.
 unfold alpha_gamma.
 
 (* square 1, naturality of Chi *)
 assert (square1: lift_B_ _ _ (lift_T_star_ R P pi) (B_Chi_R (lambda_star_TR (T_star_gamma hr))) =
    lift_B_ _ _ (Chi P) (lift_B_ _ _ (lift_T_star_ _ _ (lift_T_ R P pi)) (lambda_star_TR (T_star_gamma hr)))).
  unfold B_Chi_R; do 2 rewrite lift_B_compose; fold lift_B_; apply lift_B_extensionality; intros [j tx_]; trivial.

 rewrite square1.
 (* square 2, extra square *)
  set (tmp:=(lift_B_ _ _ (lift_T_star_ _ _ (lift_T_ R P pi)) (lambda_star_TR (T_star_gamma hr)))).
  assert (square2:
        lift_B_ _ _ (Beta_star Y) (lift_B_ _ _ (Chi P) tmp) =
        lift_B_ _ _ (Beta_star Y) (lift_B_ _ _ (lift_T_star_ _ _ beta_P) tmp) ).
   simpl; do 2 rewrite lift_B_compose; fold lift_B_; apply lift_B_extensionality; intros [j ttx]; trivial.

  fold P in square2;fold P; unfold carrier in *; rewrite square2.
  subst tmp.
  
  rewrite (lift_B_compose _ _ _ (lift_T_star_ (F_ R) (F_ P) (lift_T_ R P pi)) (lift_T_star_ (F_ P) P beta_P)).
  fold lift_B_.
  assert (foo:=lift_T_star_compose _ _ _ (lift_T_ R P pi) beta_P).
  fold P in foo.
  stepl 
  (lift_B_ _ _ (Beta_star Y)
     (lift_B_ _ _ (lift_T_star_ _ _ (fun x => beta_P (lift_T_ R P pi x))) (lambda_star_TR (T_star_gamma hr))) );
  [
  |do 2 rewrite lift_B_compose; fold lift_B_; apply lift_B_extensionality; intros; f_equal; rewrite lift_T_star_compose; trivial].
  
  (* square 3 *)
  set (tmp:=T_star_gamma hr).
  assert (square3: lift_B_ (T_star_ (F_ R)) (T_star_ (states (coalgebra_part Y)))
        (lift_T_star_ (F_ R) (states (coalgebra_part Y))
           (fun x : F_ R => beta_P (lift_T_ R P pi x))) 
        (lambda_star_TR tmp) =lambda_star Lambda P (lift_T_star_ _ _ (lift_B_ _ _ (fun x : F_ R => beta_P (lift_T_ R P pi x))) tmp)).
  generalize tmp as tsbx.
  apply lambda_star_naturality.

  rewrite square3.  
  (* square 4 *)
  fold B_ T_ P.  
  subst tmp.
  stepl (lift_B_ _ _ (Beta_star Y) (lambda_star Lambda P (lift_T_star_ _ _ alpha_P (lift_T_star_ _ _ pi hr)) ));
  [
  | do 2 f_equal; unfold T_star_gamma, alpha_P; do 2 rewrite lift_T_star_compose;
    fold R P B_; apply lift_T_star_extensionality;
    intros r; symmetry; fold R P B_ T_ gamma in hyp_lam_bisim; apply hyp_lam_bisim
  ].

  (* pentagon 5 *)
  fold P R.
  set (tmp:=lift_T_star_ R P pi hr).
  apply Lam_bisimulation_4_1_5_lambda_star_bialgebra.
  intros tx.
  generalize(Lam_bisimulation_4_1_5_lambda_star_bialgebra Lambda Y).
  intros H_lambda_star.
  apply hyp_lam_bialg.
Qed.
  
Definition is_lambda_bisimulation (S1 S2:TB_bialgebra) 
                           (lR: states (S1.(coalgebra_part)) -> states (S2.(coalgebra_part)) -> Prop) :=
 { gamma : {s1s2 : states (coalgebra_part S1) * states (coalgebra_part S2) | lR (fst s1s2) (snd s1s2)} ->
           B_ (T_ {s1s2 : states (coalgebra_part S1) * states (coalgebra_part S2) | lR (fst s1s2) (snd s1s2)}) |
    forall  (s1s2h:{s1s2 : states (coalgebra_part S1) * states (coalgebra_part S2) | lR (fst s1s2) (snd s1s2)}),
(lift_B_ _ _ (fun fr=>S1.(algebra_part)(lift_T_ _ _  (fun s1s2h_=>fst (proj1_sig s1s2h_)) fr ) ) (gamma s1s2h) = 
transition S1.(coalgebra_part) (fst (proj1_sig s1s2h)))  /\
(lift_B_ _ _ (fun fr=>S2.(algebra_part)(lift_T_ _ _  (fun s1s2h_=>snd (proj1_sig s1s2h_)) fr ) ) (gamma s1s2h) = 
transition S2.(coalgebra_part) (snd (proj1_sig s1s2h)))  }.

Definition is_lambda_bisimulation_strong (S1 S2:TB_bialgebra) 
                           (slR: states (S1.(coalgebra_part)) -> states (S2.(coalgebra_part)) -> Set) :=
 { gamma : {s1s2 : states (coalgebra_part S1) * states (coalgebra_part S2) & slR (fst s1s2) (snd s1s2)} ->
           B_ (T_ {s1s2 : states (coalgebra_part S1) * states (coalgebra_part S2) & slR (fst s1s2) (snd s1s2)}) |
    forall  (s1s2h:{s1s2 : states (coalgebra_part S1) * states (coalgebra_part S2) & slR (fst s1s2) (snd s1s2)}),
(lift_B_ _ _ (fun fr=>S1.(algebra_part)(lift_T_ _ _  (fun s1s2h_=>fst (projT1 s1s2h_)) fr ) ) (gamma s1s2h) = 
transition S1.(coalgebra_part) (fst (projT1 s1s2h)))  /\
(lift_B_ _ _ (fun fr=>S2.(algebra_part)(lift_T_ _ _  (fun s1s2h_=>snd (projT1 s1s2h_)) fr ) ) (gamma s1s2h) = 
transition S2.(coalgebra_part) (snd (projT1 s1s2h)))  }.

(* Theorem 4.1.2 in [1] *)
Theorem is_lambda_bisimulation_commute_span: forall (Lambda:T_over_B_distributive) (Xtb Ytb:TB_bialgebra) 
                           (lR: states (Xtb.(coalgebra_part)) -> states (Ytb.(coalgebra_part)) -> Prop)
                           (gamma_: is_lambda_bisimulation _ _ lR) 
                           (hr:T_star_ {s1s2 : states (coalgebra_part Xtb) * states (coalgebra_part Ytb) |lR (fst s1s2) (snd s1s2)}),
   is_lambda_bialgebra Lambda Xtb ->
   is_lambda_bialgebra Lambda Ytb ->
    let lR_crr:= {s1s2 : states (coalgebra_part Xtb) * states (coalgebra_part Ytb) |lR (fst s1s2) (snd s1s2)} in
     let h_x := fun hr => (Beta_star Xtb) (lift_T_star_ _ _ (fun s1s2h:lR_crr => fst (proj1_sig s1s2h)) hr) in
     let h_y := fun hr => (Beta_star Ytb) (lift_T_star_ _ _ (fun s1s2h:lR_crr => snd (proj1_sig s1s2h)) hr) in
       let T_star_gamma := lift_T_star_ _ _ (proj1_sig gamma_) in
         let lambda_star_TR := lambda_star Lambda (T_ lR_crr) in
           let B_Chi_R := lift_B_ _ _ (Chi lR_crr) in
             let alpha_gamma := fun hr0 => B_Chi_R (lambda_star_TR (T_star_gamma hr0)) in
      lift_B_ _ _ h_x (alpha_gamma hr) = (transition Xtb.(coalgebra_part)) (h_x hr) /\
      lift_B_ _ _ h_y (alpha_gamma hr) = (transition Ytb.(coalgebra_part)) (h_y hr).
Proof.
 intros Lambda Xtb Ytb lR [gamma hyp_gamma] tr hyp_X_bialgb hyp_Y_bialg lR_crr h_x h_y T_star_gamma lambda_star_TR B_Chi_R alpha_gamma;
 split; [subst h_x | subst h_y];
 apply (is_like_lambda_bismulation_T_star_span_bisimulation Lambda (Build_BT_coalgebroid lR_crr gamma)); trivial;
 red; simpl; intros s1s2h; destruct (hyp_gamma s1s2h) as [Hx Hy];
 [ apply Hx | apply Hy]; assumption.
Qed.


Theorem is_lambda_bisimulation_F_bisimulation_strong: forall (Lambda:T_over_B_distributive) (Xtb Ytb:TB_bialgebra) 
                           (lR: states (Xtb.(coalgebra_part)) -> states (Ytb.(coalgebra_part)) -> Prop)
                           (gamma_: is_lambda_bisimulation _ _ lR) ,
                           is_lambda_bialgebra Lambda Xtb ->
                           is_lambda_bialgebra Lambda Ytb ->
    let lR_crr:= {s1s2 : states (coalgebra_part Xtb) * states (coalgebra_part Ytb) |lR (fst s1s2) (snd s1s2)} in
     let h_x := fun hr => (Beta_star Xtb) (lift_T_star_ _ _ (fun s1s2h:lR_crr => fst (proj1_sig s1s2h)) hr) in
     let h_y := fun hr => (Beta_star Ytb) (lift_T_star_ _ _ (fun s1s2h:lR_crr => snd (proj1_sig s1s2h)) hr) in
        is_F_bisimulation_strong Xtb.(coalgebra_part) Ytb.(coalgebra_part) (fun x=>(fun y=>{hr:T_star_ lR_crr | h_x hr = x /\ h_y hr= y} )).
Proof.
 intros Lambda Xtb Ytb lR gamma_ hyp_x_bialg hyp_y_bialg lR_crr h_x h_y.
 set (T_star_gamma := lift_T_star_ _ _ (proj1_sig gamma_)).
 set (lambda_star_TR := lambda_star Lambda (T_ lR_crr)).
 set (B_Chi_R := lift_B_ _ _ (Chi lR_crr)).
 set (alpha_gamma := ( fun hr0 => B_Chi_R (lambda_star_TR (T_star_gamma hr0)) ):  T_star_ lR_crr -> B_ (T_star_ lR_crr)).
 apply (image_span_is_F_bisimulation_strong Xtb.(coalgebra_part) (Build_F_coalgebra (T_star_ lR_crr) alpha_gamma) Ytb.(coalgebra_part));
 intros s2;  
 destruct (is_lambda_bisimulation_commute_span Lambda Xtb Ytb lR gamma_ s2 hyp_x_bialg hyp_y_bialg) as [hypl hypr]; simpl in *.
 apply hypl.
 apply hypr.
Qed. 

Theorem lambda_bisimulation_included_image_span: forall (Lambda:T_over_B_distributive) (Xtb Ytb:TB_bialgebra) 
                           (lR: states (Xtb.(coalgebra_part)) -> states (Ytb.(coalgebra_part)) -> Prop)
                           (gamma_: is_lambda_bisimulation _ _ lR) 
                           (x:states Xtb.(coalgebra_part)) (y:states Ytb.(coalgebra_part)),
                           lR x y ->
                           is_lambda_bialgebra Lambda Xtb ->
                           is_lambda_bialgebra Lambda Ytb ->
    let lR_crr:= {s1s2 : states (coalgebra_part Xtb) * states (coalgebra_part Ytb) |lR (fst s1s2) (snd s1s2)} in
     let h_x := fun hr => (Beta_star Xtb) (lift_T_star_ _ _ (fun s1s2h:lR_crr => fst (proj1_sig s1s2h)) hr) in
     let h_y := fun hr => (Beta_star Ytb) (lift_T_star_ _ _ (fun s1s2h:lR_crr => snd (proj1_sig s1s2h)) hr) in
                           {hr:T_star_ lR_crr | h_x hr = x /\ h_y hr= y} .
Proof.
 intros Lambda Xtb Ytb lR gamma_ x y hyp_lR hyp_x_bialg hyp_y_bialg lR_crr h_x h_y.
 exists (T_star_coproject_ lR_crr O (exist (fun xy => lR (fst xy) (snd xy)) (x,y) hyp_lR)).
 subst h_x h_y; simpl in *; split; trivial.
Qed.

Lemma is_lambda_bisimulation_strong_F_bisimulation_strong: forall (Lambda:T_over_B_distributive) (Xtb Ytb:TB_bialgebra) 
                           (slR: states (Xtb.(coalgebra_part)) -> states (Ytb.(coalgebra_part)) -> Set)
                           (gamma_: is_lambda_bisimulation_strong _ _ slR) ,
                           is_lambda_bialgebra Lambda Xtb ->
                           is_lambda_bialgebra Lambda Ytb ->
    let slR_crr:= {s1s2 : states (coalgebra_part Xtb) * states (coalgebra_part Ytb) & slR (fst s1s2) (snd s1s2)} in
     let h_x := fun hr => (Beta_star Xtb) (lift_T_star_ _ _ (fun s1s2h:slR_crr => fst (projT1 s1s2h)) hr) in
     let h_y := fun hr => (Beta_star Ytb) (lift_T_star_ _ _ (fun s1s2h:slR_crr => snd (projT1 s1s2h)) hr) in
        is_F_bisimulation_strong Xtb.(coalgebra_part) Ytb.(coalgebra_part) (fun x=>(fun y=>{hr:T_star_ slR_crr | h_x hr = x /\ h_y hr= y} )).
Proof.
 intros Lambda Xtb Ytb slR gamma_ hyp_x_bialg hyp_y_bialg slR_crr h_x h_y.
 set (T_star_gamma := lift_T_star_ _ _ (proj1_sig gamma_)).
 set (lambda_star_TR := lambda_star Lambda (T_ slR_crr)).
 set (B_Chi_R := lift_B_ _ _ (Chi slR_crr)).
 set (alpha_gamma := ( fun hr0 => B_Chi_R (lambda_star_TR (T_star_gamma hr0)) ):  T_star_ slR_crr -> B_ (T_star_ slR_crr)).
 apply (image_span_is_F_bisimulation_strong Xtb.(coalgebra_part) (Build_F_coalgebra (T_star_ slR_crr) alpha_gamma) Ytb.(coalgebra_part));
 intros s;
 subst h_x h_y;
 destruct gamma_ as [gamma hyp_gamma].  
  apply (is_like_lambda_bismulation_T_star_span_bisimulation Lambda (Build_BT_coalgebroid slR_crr gamma) 
                                 Xtb (fun s1s2h : slR_crr => fst (projT1 s1s2h))); trivial;
  intros s1s2h; apply (hyp_gamma s1s2h).

  apply (is_like_lambda_bismulation_T_star_span_bisimulation Lambda (Build_BT_coalgebroid slR_crr gamma) 
                                 Ytb (fun s1s2h : slR_crr => snd (projT1 s1s2h))); trivial;
  intros s1s2h; apply (hyp_gamma s1s2h).
Qed.

Lemma lambda_bisimulation_strong_included_image_span: forall (Lambda:T_over_B_distributive) (Xtb Ytb:TB_bialgebra) 
                           (slR: states (Xtb.(coalgebra_part)) -> states (Ytb.(coalgebra_part)) -> Set)
                           (gamma_: is_lambda_bisimulation_strong _ _ slR) 
                           (x:states Xtb.(coalgebra_part)) (y:states Ytb.(coalgebra_part)),
                           slR x y ->
                           is_lambda_bialgebra Lambda Xtb ->
                           is_lambda_bialgebra Lambda Ytb ->
    let slR_crr:= {s1s2 : states (coalgebra_part Xtb) * states (coalgebra_part Ytb) &slR (fst s1s2) (snd s1s2)} in
     let h_x := fun hr => (Beta_star Xtb) (lift_T_star_ _ _ (fun s1s2h:slR_crr => fst (projT1 s1s2h)) hr) in
     let h_y := fun hr => (Beta_star Ytb) (lift_T_star_ _ _ (fun s1s2h:slR_crr => snd (projT1 s1s2h)) hr) in
                           {hr:T_star_ slR_crr | h_x hr = x /\ h_y hr= y} .
Proof.
 intros Lambda Xtb Ytb slR gamma_ x y hyp_slR hyp_x_bialg hyp_y_bialg slR_crr h_x h_y.
 exists (T_star_coproject_ slR_crr O (existT (fun xy => slR (fst xy) (snd xy)) (x,y) hyp_slR)).
 subst h_x h_y; simpl in *; split; trivial.
Qed.

Lemma is_lambda_bisimulation_F_bisimulation_strong_like: forall (Lambda:T_over_B_distributive) (Rbt:BT_coalgebroid) (Xtb Ytb:TB_bialgebra)
                           (f: Rbt.(bs_states) -> states Xtb.(coalgebra_part))
                           (g: Rbt.(bs_states) -> states Ytb.(coalgebra_part)),
                           is_lambda_bialgebra Lambda Xtb ->
                           is_lambda_bialgebra Lambda Ytb ->
                           (forall rtb, is_like_lambda_bismulation Rbt Xtb f rtb) ->
                           (forall rtb, is_like_lambda_bismulation Rbt Ytb g rtb) ->
                         let h_f := fun hr => (Beta_star Xtb) (lift_T_star_ _ _ f hr) in 
                         let h_g := fun hr => (Beta_star Ytb) (lift_T_star_ _ _ g hr) in
        is_F_bisimulation_strong Xtb.(coalgebra_part) Ytb.(coalgebra_part) (fun x=>(fun y=>{hr : T_star_ Rbt.(bs_states)| h_f hr = x /\ h_g hr = y})).
Proof.
 intros Lambda Rbt Xtb Ytb f g hyp_x_bialg hyp_y_bialg hyp_f hyp_g h_f h_g.
 set (T_star_gamma := lift_T_star_ _ _ Rbt.(bs_transition)).
 set (lambda_star_TR := lambda_star Lambda (T_ Rbt.(bs_states))).
 set (B_Chi_R := lift_B_ _ _ (Chi Rbt.(bs_states))).
 set (alpha_gamma := ( fun hr0 => B_Chi_R (lambda_star_TR (T_star_gamma hr0)) ): T_star_ Rbt.(bs_states) -> B_ (T_star_ Rbt.(bs_states))).
 apply (image_span_is_F_bisimulation_strong Xtb.(coalgebra_part) (Build_F_coalgebra (T_star_ Rbt.(bs_states)) alpha_gamma) Ytb.(coalgebra_part));
 intros s2.
 subst h_f; apply is_like_lambda_bismulation_T_star_span_bisimulation; trivial.
 subst h_g; apply is_like_lambda_bismulation_T_star_span_bisimulation; trivial.
Qed.

Lemma lambda_bisimulation_included_image_span_like: forall (Lambda:T_over_B_distributive) (Rbt:BT_coalgebroid) (Xtb Ytb:TB_bialgebra)
                           (f: Rbt.(bs_states) -> states Xtb.(coalgebra_part))
                           (g: Rbt.(bs_states) -> states Ytb.(coalgebra_part)),
                           is_lambda_bialgebra Lambda Xtb ->
                           is_lambda_bialgebra Lambda Ytb ->
                           (forall rtb, is_like_lambda_bismulation Rbt Xtb f rtb) ->
                           (forall rtb, is_like_lambda_bismulation Rbt Ytb g rtb) ->
                         let h_f := fun hr => (Beta_star Xtb) (lift_T_star_ _ _ f hr) in 
                         let h_g := fun hr => (Beta_star Ytb) (lift_T_star_ _ _ g hr) in
                          forall r, {hr : T_star_ (bs_states Rbt) | h_f hr = f r /\ h_g hr = g r}.
Proof.
 intros Lambda Rbt Xtb Ytb f g hyp_x_bialg hyp_y_bialg hyp_f hyp_g h_f h_g r.
 exists (T_star_coproject_ Rbt.(bs_states) O r).
 subst h_f h_g; simpl in *; split; trivial.
Qed.

Theorem lambda_coinduction_lambda_bialgebras: forall (Lambda:T_over_B_distributive) (Xtb Ytb:TB_bialgebra)
                           (lR: states (Xtb.(coalgebra_part)) -> states (Ytb.(coalgebra_part)) -> Prop)
                           (gamma_: is_lambda_bisimulation _ _ lR) 
                           (x:states Xtb.(coalgebra_part)) (y:states Ytb.(coalgebra_part)),
                           lR x y -> 
                           is_lambda_bialgebra Lambda Xtb ->
                           is_lambda_bialgebra Lambda Ytb ->
                           (maximal_bisimulation Xtb.(coalgebra_part) Ytb.(coalgebra_part) x y).
Proof.
 intros Lambda Xtb Ytb lR gamma_ x y hyp_lR hyp_x_bialg hyp_y_bialg.
 destruct (maximal_bisimulation_is_maximal Xtb.(coalgebra_part) Ytb.(coalgebra_part)) as [_ hyp_max].
 set (lR_crr:= {s1s2 : states (coalgebra_part Xtb) * states (coalgebra_part Ytb) |lR (fst s1s2) (snd s1s2)}).
 set (h_x := fun hr => (Beta_star Xtb) (lift_T_star_ _ _ (fun s1s2h:lR_crr => fst (proj1_sig s1s2h)) hr)).
 set (h_y := fun hr => (Beta_star Ytb) (lift_T_star_ _ _ (fun s1s2h:lR_crr => snd (proj1_sig s1s2h)) hr)).

 apply (hyp_max (fun x=>(fun y=>{hr:T_star_ lR_crr | h_x hr = x /\ h_y hr= y} ))).
 exists (is_lambda_bisimulation_F_bisimulation_strong Lambda Xtb Ytb lR gamma_ hyp_x_bialg hyp_y_bialg); trivial.
 apply (lambda_bisimulation_included_image_span Lambda Xtb Ytb lR gamma_ x y hyp_lR hyp_x_bialg hyp_y_bialg).
Qed.

Lemma lambda_coinduction_lambda_bialgebras_strong: forall (Lambda:T_over_B_distributive) (Xtb Ytb:TB_bialgebra)
                           (slR: states (Xtb.(coalgebra_part)) -> states (Ytb.(coalgebra_part)) -> Set)
                           (gamma_: is_lambda_bisimulation_strong _ _ slR) 
                           (x:states Xtb.(coalgebra_part)) (y:states Ytb.(coalgebra_part)),
                           slR x y -> 
                           is_lambda_bialgebra Lambda Xtb ->
                           is_lambda_bialgebra Lambda Ytb ->
                           (maximal_bisimulation Xtb.(coalgebra_part) Ytb.(coalgebra_part) x y).
Proof.
 intros Lambda Xtb Ytb slR gamma_ x y hyp_slR hyp_x_bialg hyp_y_bialg.
 destruct (maximal_bisimulation_is_maximal Xtb.(coalgebra_part) Ytb.(coalgebra_part)) as [_ hyp_max].
 set (slR_crr:= {s1s2 : states (coalgebra_part Xtb) * states (coalgebra_part Ytb) &slR (fst s1s2) (snd s1s2)}).
 set (h_x := fun hr => (Beta_star Xtb) (lift_T_star_ _ _ (fun s1s2h:slR_crr => fst (projT1 s1s2h)) hr)).
 set (h_y := fun hr => (Beta_star Ytb) (lift_T_star_ _ _ (fun s1s2h:slR_crr => snd (projT1 s1s2h)) hr)).

 apply (hyp_max (fun x=>(fun y=>{hr:T_star_ slR_crr | h_x hr = x /\ h_y hr= y} ))).
 exists (is_lambda_bisimulation_strong_F_bisimulation_strong Lambda Xtb Ytb slR gamma_ hyp_x_bialg hyp_y_bialg); trivial.
 apply (lambda_bisimulation_strong_included_image_span Lambda Xtb Ytb slR gamma_ x y hyp_slR hyp_x_bialg hyp_y_bialg).
Qed.


Lemma lambda_coinduction_lambda_bialgebras_like: forall (Lambda:T_over_B_distributive) (Rbt:BT_coalgebroid) (Xtb Ytb:TB_bialgebra)
                           (f: Rbt.(bs_states) -> states Xtb.(coalgebra_part))
                           (g: Rbt.(bs_states) -> states Ytb.(coalgebra_part)),
                           is_lambda_bialgebra Lambda Xtb ->
                           is_lambda_bialgebra Lambda Ytb ->
                           (forall rtb, is_like_lambda_bismulation Rbt Xtb f rtb) ->
                           (forall rtb, is_like_lambda_bismulation Rbt Ytb g rtb) ->
                           forall r, (maximal_bisimulation Xtb.(coalgebra_part) Ytb.(coalgebra_part) (f r) (g r)).
Proof.
 intros Lambda Rbt Xtb Ytb f g hyp_x_bialg hyp_y_bialg hyp_f hyp_g r.
 destruct (maximal_bisimulation_is_maximal Xtb.(coalgebra_part) Ytb.(coalgebra_part)) as [_ hyp_max].

 set (h_f := fun hr => (Beta_star Xtb) (lift_T_star_ _ _ f hr)).
 set (h_g := fun hr => (Beta_star Ytb) (lift_T_star_ _ _ g hr)).
 apply (hyp_max (fun x=>(fun y=>{hr:T_star_ Rbt.(bs_states) | h_f hr = x /\ h_g hr = y} ))).

 exists (is_lambda_bisimulation_F_bisimulation_strong_like Lambda Rbt Xtb Ytb f g hyp_x_bialg hyp_y_bialg hyp_f hyp_g); trivial.
 apply (lambda_bisimulation_included_image_span_like Lambda Rbt Xtb Ytb f g hyp_x_bialg hyp_y_bialg hyp_f hyp_g).
Qed.

(* weak version of Theorem 3.2.3 in [1]. *)
Theorem weakly_final_lambda_bialgebra : forall (Lambda: T_over_B_distributive),
  is_lambda_bialgebra Lambda (Build_TB_bialgebra w (Beta Lambda)).
Proof.
 intros [lam_ nat_lam_] tx.
 assert (hyp:=commutativity_F_unfold (Build_F_coalgebra (T_ w.(states)) (fun tw=> lam_ _ (lift_T_ _ _ w.(transition) tw))) tx). 
 symmetry.
 apply hyp.
Qed.

Theorem lambda_coinduction: forall (Lambda:T_over_B_distributive) (lR: w.(states) -> w.(states) -> Prop) (x y:w.(states)),
       lR x y -> 
     is_lambda_bisimulation (Build_TB_bialgebra w (Beta Lambda)) 
                            (Build_TB_bialgebra w (Beta Lambda)) lR ->
                             x (=) y.
Proof.
 intros Lambda lR x y hyp_lR hyp_lam_bisim.
 apply (lambda_coinduction_lambda_bialgebras Lambda 
                            (Build_TB_bialgebra w (Beta Lambda))
                            (Build_TB_bialgebra w (Beta Lambda)) lR hyp_lam_bisim x y hyp_lR);
 apply weakly_final_lambda_bialgebra. 
Qed.

Theorem lambda_coinduction_strong: forall (Lambda:T_over_B_distributive) (slR: w.(states) -> w.(states) -> Set) (x y:w.(states)),
       slR x y -> 
     is_lambda_bisimulation_strong (Build_TB_bialgebra w (Beta Lambda)) 
                            (Build_TB_bialgebra w (Beta Lambda)) slR ->
                             x (=) y.
Proof.
 intros Lambda slR x y hyp_slR hyp_lam_bisim.
 apply (lambda_coinduction_lambda_bialgebras_strong Lambda 
                            (Build_TB_bialgebra w (Beta Lambda))
                            (Build_TB_bialgebra w (Beta Lambda)) slR hyp_lam_bisim x y hyp_slR);
 apply weakly_final_lambda_bialgebra. 
Qed.


Lemma Lam_coiterator_uniqueness: forall (Lambda:T_over_B_distributive) (Xbt: BT_coalgebroid)
                                 (f g:Xbt.(bs_states) -> w.(states)),
       (forall x,  w.(transition) (f x) = lift_B_ _ _ (Beta Lambda) (lift_B_ _ _ (lift_T_ _ _ f) (Xbt.(bs_transition) x))) ->
       (forall x,  w.(transition) (g x) = lift_B_ _ _ (Beta Lambda) (lift_B_ _ _ (lift_T_ _ _ g) (Xbt.(bs_transition) x))) ->
       forall x, f x (=) g x.
Proof.
 intros Lambda Xbt f g hyp_f hyp_g.
 apply (lambda_coinduction_lambda_bialgebras_like Lambda Xbt 
                            (Build_TB_bialgebra w (Beta Lambda))
                            (Build_TB_bialgebra w (Beta Lambda)) f g).  
 apply weakly_final_lambda_bialgebra.
 apply weakly_final_lambda_bialgebra.
 unfold is_like_lambda_bismulation; intros rtb; symmetry; simpl in *; rewrite (hyp_f rtb); rewrite lift_B_compose; trivial.
 unfold is_like_lambda_bismulation; intros rtb; symmetry; simpl in *; rewrite (hyp_g rtb); rewrite lift_B_compose; trivial.
Qed.

End Lambda_Bisimulation_theory.
