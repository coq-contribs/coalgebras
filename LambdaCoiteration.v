(************************************************************************)
(* Copyright 2008 Milad Niqui                                           *)
(* This file is distributed under the terms of the                      *)
(* GNU Lesser General Public License Version 3                          *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses/lgpl.txt>              *)
(************************************************************************)

Require Export WeaklyFinalCoalgebra.

(** Formalisation of the Lambda-coiteration definition scheme [1].

[1] Falk Bartels. On Generalised Coinduction and Probabilistic specification Formats:
   Distributive laws in coalgebraic modelling. PhD thesis, VU Amsterdam, 2004.

*)


Module Lambda_Coiteration_theory (MB:Weakly_Final_Coalgebra) (MS:Set_Functor).

Import MB MS.
Export MB MS.

Module MB_Coalgebra_Theory := Set_Coalgebra_theory MB.

Definition B_:=MB.F_.
Definition lift_B_id:=MB.lift_F_id.
Definition lift_B_compose:=MB.lift_F_compose.
Definition lift_B_:=MB.lift_F_.
Definition lift_B_extensionality:=MB.lift_F_extensionality.
Definition B_coalgebra_compose:=MB_Coalgebra_Theory.F_coalgebra_compose.
Definition rel_image_lift_B_:=MB.rel_image_lift_F_.
Definition lift_B_extensionality_bisim:=MB.lift_F_extensionality_bisim.

Module MS_Functor_Iter_Theory := Set_Functor_Iter_theory MS.

Definition S_:=MS.F_.
Definition lift_S_:=MS.lift_F_.
Definition lift_S_id:=MS.lift_F_id.
Definition lift_S_compose:=MS.lift_F_compose.
Definition lift_S_extensionality:=MS.lift_F_extensionality.
Definition S_iter := MS_Functor_Iter_Theory.F_iter.
Definition lift_S_iter := MS_Functor_Iter_Theory.lift_F_iter.
Definition S_iter_S :=  MS_Functor_Iter_Theory.F_iter_S.
Definition lift_S_iter_extensionality := MS_Functor_Iter_Theory.lift_F_iter_extensionality.
Definition lift_S_iter_compose := MS_Functor_Iter_Theory.lift_F_iter_compose.

Let H_ (X:Set) := { j:nat & { x:(S_iter j X) & unit }}.

Let lift_H_ (X Y:Set) (f:X->Y) (hx: H_ X) : H_ Y :=   
        let (j,tmp):= hx in let (s_ix,_) := tmp in existT _ j (existT _ (lift_S_iter _ _ f j s_ix) tt).

Let lift_H_compose (X Y Z:Set) (g:X->Y) (f:Y->Z) hx: 
   (fun hx0 => lift_H_ Y Z f (lift_H_ X Y g hx0)) hx = lift_H_ X Z (fun x => f (g x)) hx.
Proof.
 intros X Y Z g f [j [x0 hyp]]. 
 simpl.
 rewrite lift_S_iter_compose. 
 trivial.
Defined.

Let H_coproject_ (X:Set) (j:nat) (x: S_iter j X) : H_ X := existT _ j (existT _ x tt).

Let infinite_case_analysis (X Y:Set) (fs:forall j:nat, S_iter j X -> Y)  (h:H_ X) : Y := 
    let (i,tmp):= h in let (x,_) := tmp in fs i x.

(* Note that this is not a coalgebra in the sense of Set_Coalgebra,
because we do not require BS to be a Set_Fucntor. *)

Record BS_coalgebroid : Type := 
{ bs_states : Set 
; bs_transition: bs_states -> B_ (S_ bs_states) 
}.

Record S_over_B_distributive : Type :=
{ lambda_ : forall (X:Set) , S_ (B_ X) -> B_ (S_ X)
; lambda_is_natural_: forall (X Y:Set) (f:X->Y) (sbx:S_ (B_ X)), 
     lambda_ _ (lift_S_ _ _ (lift_B_ _ _ f) sbx) = lift_B_ (S_ X) (S_ Y) (lift_S_ _ _ f) (lambda_ _ sbx)
}.

Fixpoint lambda_iter_ (Lambda : S_over_B_distributive) (j : nat) (X:Set) {struct j} :
         S_iter j (B_ X) -> B_ (S_iter j X) :=
         match Lambda with
         | Build_S_over_B_distributive lam_ n_ =>
             match j
             with
             | O => fun (x : B_ X) => x
             | S j' => fun (s_ix : S_iter j' (S_ (B_ X))) =>
                 lambda_iter_ (Build_S_over_B_distributive lam_ n_) j' (S_ X) (lift_S_iter (S_ (B_ X)) (B_ (S_ X)) (lam_ X) j' s_ix)
             end
         end.

Let lambda_star (Lambda:S_over_B_distributive) (X:Set) : H_ (B_ X) -> B_ (H_ X) :=
   infinite_case_analysis _ _ (fun j s_ibx => lift_B_ _ _ (H_coproject_ X j) (lambda_iter_ Lambda j X s_ibx)).

Let Chi (X:Set) : H_ (S_ X) -> (H_ X) := infinite_case_analysis _ _ (fun j => H_coproject_ X (S j)).

Definition Lam_coiterator (Lambda:S_over_B_distributive) (BS: BS_coalgebroid) : BS.(bs_states) -> w.(states) :=
   match BS with
   | Build_BS_coalgebroid X X_tr =>
     let i0 := H_coproject_ X 0 in
       let H_phi := lift_H_ _ _ X_tr in
         let lambda_star_SX := lambda_star Lambda (S_ X) in
           let B_Chi_X := lift_B_ _ _ (Chi X) in
             let h := F_unfold (Build_F_coalgebra (H_ X) (fun x=> B_Chi_X (lambda_star_SX (H_phi x)))) in
             fun x => h (i0 x)
   end.


Definition Beta (Lambda:S_over_B_distributive) : S_ w.(states) -> w.(states):=
       match Lambda with
       | Build_S_over_B_distributive lam_ _=>
           F_unfold (Build_F_coalgebra _ (fun s_bx=> lam_ _ (lift_S_ _ _ (transition w) s_bx)))
       end.

Fixpoint reformat_S_iter_S_right (j : nat) (X:Set) : S_iter (S j) X -> S_ (S_iter j X) :=
  match j 
  with
  | O =>  fun sx => sx
  | S j' =>  reformat_S_iter_S_right j' (S_ X)
  end.

Let bracket_S_j_fun  X j x0 := lift_S_ _ _ (H_coproject_ X j) (reformat_S_iter_S_right j _ x0).

Let reformat_S_iter_S_right_property:forall (j:nat) (X Y:Set) (f:X->Y) (ssx:S_iter (S j) X),
   lift_S_ _ _ (lift_S_iter _ _ f j) (reformat_S_iter_S_right j X ssx) = reformat_S_iter_S_right j Y (lift_S_iter X Y f (S j) ssx).
Proof.
 induction j; intros X Y f ssx; trivial.
 stepr (reformat_S_iter_S_right j (S_ Y) (lift_S_iter _ _ (lift_S_ _ _ f) (S j) ssx)); trivial.
 rewrite <- IHj; trivial.
Defined.

Let S_iter_lambda_iter: forall (Lambda:S_over_B_distributive) (j : nat) (X:Set) (sbx:S_iter (S j) (B_ X)), 
   lift_B_ _ _ (reformat_S_iter_S_right j X) (lambda_iter_ Lambda (S j) X sbx) =
   Lambda.(lambda_) (S_iter j X) (lift_S_ _ _ (lambda_iter_ Lambda j X) (reformat_S_iter_S_right j (B_ X) sbx)).
Proof.
 intros [lam nat_lam]; induction j. 
  intros X sbx.

  transitivity (lift_B_ (S_ X) (S_ X) (lift_S_ X X (fun x : X => x)) (lam X sbx)).
   simpl.
   apply lift_B_extensionality; apply lift_S_id.
   transitivity (lam X (lift_S_ (B_ X) (B_ X) (lift_B_ X X (fun x : X => x)) sbx)).
    rewrite nat_lam; trivial.
    assert (eq_ext:lift_S_ (B_ X) (B_ X) (lift_B_ X X (fun x : X => x)) sbx =
                   lift_S_ (B_ X) (B_ X) (fun x : B_ X => x) sbx).
     apply lift_S_extensionality.
     intros bx; symmetry; apply lift_B_id.
     rewrite eq_ext; trivial.

  intros X sbx.
  stepl (lift_B_ _ _ (reformat_S_iter_S_right j (S_ X)) 
                (lambda_iter_ (Build_S_over_B_distributive lam nat_lam) (S j) (S_ X) (lift_S_iter _ _ (lam X) (S j) sbx))); trivial.
  rewrite IHj.
  rewrite <- reformat_S_iter_S_right_property.
  rewrite lift_S_compose.
  trivial.
Defined.


Let Lam_coiterator_4_2_2_naturality_right: forall (Lambda:S_over_B_distributive) X (hsbx:H_ (S_ (B_ X))), 
   Lambda.(lambda_) _ (lift_S_ _ _ (lambda_star Lambda X) (infinite_case_analysis _ (S_ (H_ (B_ X))) (bracket_S_j_fun _) hsbx)) =
   lift_B_ _ (S_ (H_ X)) (infinite_case_analysis _ (S_ (H_ X)) (bracket_S_j_fun X)) (lambda_star Lambda _ (lift_H_ _ _ (Lambda.(lambda_) X) hsbx)).
Proof.
 intros [lam nat_lam] X hsbx.
 simpl.
 unfold H_ in hsbx.
 destruct hsbx as [j [sbx hyp_]].
 simpl.
 rewrite lift_B_compose.
 simpl.
 stepl (lift_B_ _ (S_ (H_ X)) (fun x : S_iter j (S_ X) => bracket_S_j_fun X j x) (lambda_iter_ (Build_S_over_B_distributive lam nat_lam) (S j) _ sbx)); trivial.
 unfold bracket_S_j_fun.
 rewrite lift_S_compose. 
 stepr (lam _  (lift_S_ _ _ (fun sjbx0: S_iter j (B_ X) => lift_B_ _ _ (H_coproject_ X j) (lambda_iter_ (Build_S_over_B_distributive lam nat_lam) j X sjbx0))  (reformat_S_iter_S_right j (B_ X) sbx))); trivial.
 rewrite <- lift_S_compose with (Y:=B_ (S_iter j X)).
 rewrite (nat_lam (S_iter j X) _ (H_coproject_ X j)).
 simpl.
 assert (lambda_iter_j_property:=S_iter_lambda_iter (Build_S_over_B_distributive lam nat_lam) j X sbx).
 simpl in lambda_iter_j_property.
 fold lift_S_.
 rewrite <- lambda_iter_j_property.
 rewrite lift_B_compose.
 trivial.
Defined.


Let Lam_coiterator_4_2_2_naturality_left: forall (Lambda:S_over_B_distributive) X (hsbx:H_ (S_ (B_ X))),
    lift_B_ _ _ (Chi X) (lambda_star Lambda (S_ X) (lift_H_ _ _ (Lambda.(lambda_) X) hsbx)) =
    lambda_star Lambda X (Chi (B_ X) hsbx).
Proof.
 intros [lam nat_lam] X hsbx.
 simpl. 
 unfold H_ in hsbx.
 destruct hsbx as [j [sbx hyp_]].
 stepl (   lift_B_ (H_ (S_ X)) (H_ X) (Chi X)
     (lift_B_ (S_iter j (S_ X)) (H_ (S_ X)) (H_coproject_ (S_ X) j)
        (lambda_iter_ (Build_S_over_B_distributive lam nat_lam) (S j) X sbx))); trivial.
 stepr  ( lambda_star (Build_S_over_B_distributive lam nat_lam) X
     (Chi (B_ X) (H_coproject_ (S_ (B_ X)) j sbx))); trivial.
 rewrite lift_B_compose.
 trivial.
Defined.
 
Let Lam_coiterator_4_11_bisim : forall (Lambda:S_over_B_distributive) (BS: BS_coalgebroid) (x:S_ BS.(bs_states)),
   let X:=BS.(bs_states) in
    let X_tr := BS.(bs_transition) in
     let i1 := H_coproject_ X 1 in
       let H_phi := lift_H_ _ _ X_tr in
         let lambda_star_SX := lambda_star Lambda (S_ X) in
           let B_Chi_X := lift_B_ _ _ (Chi X) in
             let h := F_unfold (Build_F_coalgebra (H_ X) (fun x=> B_Chi_X (lambda_star_SX (H_phi x)))) in
               h (i1 x) (=) (Beta Lambda) (lift_S_ _ _ (Lam_coiterator Lambda (Build_BS_coalgebroid X X_tr)) x).
Proof.
 intros Lambda [X X_tr] sx.
 unfold bs_states.
 unfold bs_states in sx.
 unfold bs_transition.
 set (h := F_unfold (Build_F_coalgebra (H_ X) (fun x=> 
         lift_B_ (H_ (S_ X)) (H_ X) (Chi X)
           (lambda_star Lambda (S_ X) (lift_H_ X (B_ (S_ X)) X_tr x))))).
 simpl in h.

 (* 1 *)
 assert (triangle1: lift_S_ _ _ (Lam_coiterator Lambda (Build_BS_coalgebroid X X_tr)) sx=
                    lift_S_ _ _ h (lift_S_ _ _ (H_coproject_ X 0) sx));
 [ rewrite (lift_S_compose); trivial |].
 unfold bs_states in triangle1. 
 rewrite triangle1.

 unfold S_iter.
 set (bracket_S_j:= bracket_S_j_fun X).
 (* 2 *)
 assert (triangle2:lift_S_ X (H_ X) (H_coproject_ X 0) sx=
                   infinite_case_analysis (S_ X) (S_ (H_ X)) bracket_S_j (H_coproject_ (S_ X) 0 sx));
 trivial.
 simpl; rewrite triangle2.
 (* 3 *)
 assert (triangle3: H_coproject_ X 1 sx=Chi X (H_coproject_ (S_ X) 0 sx)); trivial.
 rewrite triangle3.
 set (F1:=fun hsx => h (Chi X hsx)).
 set (F2:=fun hsx => Beta Lambda (lift_S_ _ _ h  (infinite_case_analysis (S_ X) (S_ (H_ X)) bracket_S_j hsx))).
 change (F1 (H_coproject_ (S_ X) 0 sx)(=)F2 (H_coproject_ (S_ X) 0 sx)).
 destruct Lambda as [lam nat_lam]. 
  set (psi:=fun sx0 => lam (S_ X) ((lift_S_ _ _ X_tr) sx0)).
  set (alpha_psi:= fun hsx => 
           lift_B_ _ _ (Chi (S_ X)) (lambda_star (Build_S_over_B_distributive lam nat_lam) _ (lift_H_ _ _ psi hsx))).  
  set (HSX_as_coalgebra:=Build_F_coalgebra (H_ (S_ X)) alpha_psi).
  set (alpha_phi:=fun x=> lift_B_ _ _ (Chi X) ((lambda_star (Build_S_over_B_distributive lam nat_lam) (S_ X)) (lift_H_ _ _ X_tr x))).
  set (HX_as_coalgebra:=Build_F_coalgebra (H_ X) alpha_phi).
  apply (F_unique HSX_as_coalgebra).

   (* lower route is a coalgebra map *)
    assert (h_is_coalgebra_map:=commutativity_F_unfold HX_as_coalgebra).
    assert (Chi_X_is_coalgebra_map:forall s0, HX_as_coalgebra.(transition) (Chi X s0) =
                                 lift_B_ _ _ (Chi X) (HSX_as_coalgebra.(transition) s0)).
     intros.
     unfold HX_as_coalgebra, HSX_as_coalgebra.
     simpl; trivial.
     unfold alpha_phi, alpha_psi.
     (* 4 *)
     assert (triangle4:lift_H_ _ _ (lam (S_ X)) (lift_H_ _ _ (lift_S_ _ _ X_tr) s0)=
                       (lift_H_ (S_ X) (B_ (S_ (S_ X))) psi s0)).
     rewrite lift_H_compose; trivial.

     fold S_; rewrite <- triangle4.
     (* 5 *)
     assert (square5:lift_H_ X (B_ (S_ X)) X_tr (Chi X s0)=Chi (B_ (S_ X)) (lift_H_ _ _ (lift_S_ _ _ X_tr) s0)).
     destruct s0 as [j [sx_]]; trivial.

     rewrite square5.
     rewrite Lam_coiterator_4_2_2_naturality_left; trivial.
    unfold F1.  
    apply (B_coalgebra_compose HSX_as_coalgebra HX_as_coalgebra w);[exact Chi_X_is_coalgebra_map|exact h_is_coalgebra_map].
   (* upper route is a coalgebra map *)
    set (alpha_sigma:=fun x=> lam _ (lift_S_ _ _ alpha_phi x)).
    set (SHX_as_coalgebra := Build_F_coalgebra (S_ (H_ X)) alpha_sigma).
    set (alpha_omega:=fun x=> lam _ (lift_S_ _ _ w.(transition) x)).
    set (S_Str_as_coalgebra := Build_F_coalgebra (S_ w.(states)) alpha_omega).
    unfold F2; intros hsx.

    rewrite (B_coalgebra_compose HSX_as_coalgebra SHX_as_coalgebra w (infinite_case_analysis (S_ X) (S_ (H_ X)) bracket_S_j) 
                   (fun shx => (Beta (Build_S_over_B_distributive lam nat_lam) (lift_S_ (H_ X) w.(states) h shx)))     ); trivial.

     clear hsx; intros hsx.
     simpl.
     unfold alpha_psi.
     (* 6 *)
     assert (triangle4:lift_H_ _ _ (lam (S_ X)) (lift_H_ _ _ (lift_S_ _ _ X_tr) hsx)=
                       (lift_H_ (S_ X) (B_ (S_ (S_ X))) psi hsx)).
     rewrite lift_H_compose; trivial.

     fold S_; rewrite <- triangle4.
     (* 7 *) 
     assert (square7:forall hssx, infinite_case_analysis (S_ X) (S_ (H_ X)) bracket_S_j (Chi (S_ X) hssx) =
                                 lift_S_ _ _ (Chi X) (infinite_case_analysis _ _ (bracket_S_j_fun (S_ X)) hssx)).
     intros [j [ssx hyp]]; unfold bracket_S_j_fun; simpl; rewrite lift_S_compose; trivial.

     rewrite (lift_B_compose).  
     fold S_.
     set (bx:=(lambda_star (Build_S_over_B_distributive lam nat_lam)  (S_ (S_ X))
                 (lift_H_ _ _ (lam (S_ X)) (lift_H_ (S_ X) (S_ (B_ (S_ X))) (lift_S_ X (B_ (S_ X)) X_tr) hsx)))).
     rewrite (lift_B_extensionality _ (S_ (H_ X)) (fun hssx=> infinite_case_analysis (S_ X) (S_ (H_ X)) bracket_S_j (Chi (S_ X) hssx))
                           (fun hssx => lift_S_ _ _ (Chi X) (infinite_case_analysis _ (S_ (H_ (S_ X))) (bracket_S_j_fun _) hssx)) bx square7).
     rewrite <- lift_B_compose with (Y:=S_ (H_ (S_ X))).
     subst bx.
     rewrite <- Lam_coiterator_4_2_2_naturality_right.
     unfold alpha_sigma, alpha_phi.
     rewrite <- lift_S_compose with (Y:=B_ (H_ (S_ X))).
     rewrite <- lift_S_compose with (Y:=H_ (B_ (S_ X))).
     (* 8 *)
     assert (square8:lift_S_ _ _ (lift_H_ X (B_ (S_ X)) X_tr) (infinite_case_analysis _ _ bracket_S_j hsx)=
                     infinite_case_analysis _ _ (bracket_S_j_fun (B_ (S_ X))) (lift_H_ _ _ (lift_S_ X (B_ (S_ X)) X_tr) hsx)).
      clear sx triangle1 triangle2 triangle3; destruct hsx as [j [sx hyp]].
      unfold bracket_S_j, bracket_S_j_fun; simpl.
      assert (square8_1:forall ssx,lift_S_ (H_ X) (H_ (B_ (S_ X))) (lift_H_ X (B_ (S_ X)) X_tr) (lift_S_ _ _ (H_coproject_ X j) ssx) =
                                  lift_S_ _ _ (H_coproject_ (B_ (S_ X)) j) (lift_S_ _ _ (lift_S_iter _ _ X_tr j) ssx)).
      intros ssx; do 2 rewrite lift_S_compose; apply lift_S_extensionality; trivial.

      rewrite square8_1.
      rewrite reformat_S_iter_S_right_property; trivial.

     fold lift_S_; fold S_ in square8; rewrite square8.
     rewrite (nat_lam _ _ (Chi X)); trivial.

    intros shx; 
    rewrite (B_coalgebra_compose SHX_as_coalgebra S_Str_as_coalgebra w (lift_S_ _ _ h) (Beta (Build_S_over_B_distributive lam nat_lam))); trivial;  clear shx hsx.

     intros shx.
     unfold S_Str_as_coalgebra, SHX_as_coalgebra, alpha_omega, alpha_sigma, transition at 2.
     rewrite lift_S_compose.
     assert  (S_lifts_h_finality:forall shx, lift_S_ _ _ (fun hx => transition w (h hx)) shx= 
                                             lift_S_ _ _ (fun hx=>lift_B_ _ _ h (alpha_phi hx)) shx).
      clear shx; intros shx; apply lift_S_extensionality; apply (commutativity_F_unfold HX_as_coalgebra).
     rewrite S_lifts_h_finality.
     rewrite <- lift_S_compose with (Y:=B_ (H_ X)).

     assert (rwt_tmp:=nat_lam (H_ X) w.(states) h (lift_S_ _ (B_ (H_ X)) alpha_phi shx)).
     fold lift_S_ S_ B_; fold B_ in rwt_tmp. 
     rewrite rwt_tmp.
     trivial.

     intros sstr; apply commutativity_F_unfold.
Defined.


Lemma commutativity_Lam_coiterator_rel_image_lifting (Lambda:S_over_B_distributive) (BS: BS_coalgebroid) (x:BS.(bs_states)) : 
rel_image_lift_B_ w w bisimilar (w.(transition) (Lam_coiterator Lambda BS x))
         ( lift_B_ _ _ (Beta Lambda) (lift_B_ _ _  (lift_S_ _ _ (Lam_coiterator Lambda BS)) (bs_transition BS x))).
Proof.
 intros Lambda [X X_tr] x.
 unfold Lam_coiterator.
 rewrite (commutativity_F_unfold
(Build_F_coalgebra (H_ X)
           (fun x0 : H_ X =>
            lift_B_ (H_ (S_ X)) (H_ X) (Chi X)
              (lambda_star Lambda (S_ X) (lift_H_ X (B_ (S_ X)) X_tr x0)))) (H_coproject_ X 0 x)).
 set (i0:=H_coproject_ X 0).
 set (i1:=H_coproject_ X 1).
 set (H_phi:=lift_H_ _ _ X_tr).
 set (lambda_star_SX := lambda_star Lambda (S_ X)).
 set (B_Chi_X := lift_B_ _ _ (Chi X)).
 set (h := F_unfold (Build_F_coalgebra (H_ X) (fun x=> B_Chi_X (lambda_star_SX (H_phi x))))).
 unfold transition, bs_transition, bs_states.
 assert (rwt_tmp:=lift_B_compose _ _ _ (lift_S_ _ _  (fun x0 : X => h (i0 x0))) (Beta Lambda) (X_tr x)).
 fold S_ lift_B_; fold S_ lift_B_ in rwt_tmp; 
 rewrite rwt_tmp.

 (* square 1 *)
 assert (square1:(H_coproject_  (B_ (S_ X)) 0 ) (X_tr x) = H_phi (i0 x)); trivial.
 rewrite <- square1.
 (* triangle 2 *)
 assert (triangle2:(lift_B_ _ _ (H_coproject_  (S_ X) 0 )) (X_tr x) = (lambda_star_SX (H_coproject_ (B_ (S_ X)) 0 (X_tr x)))); [destruct Lambda; trivial|].
 rewrite <- triangle2.
 (* triangle 3 *)
 assert (triangle3:(lift_B_ _ _ (H_coproject_ X 1) (X_tr x))=B_Chi_X (lift_B_ _ _ (H_coproject_ (S_ X) 0) (X_tr x)));
 [unfold B_Chi_X; rewrite lift_B_compose; apply lift_B_extensionality; trivial|].
 rewrite <- triangle3.
 unfold S_iter.
 clear rwt_tmp. assert (rwt_tmp:=(lift_B_compose _ _ _ (H_coproject_ X 1) h (X_tr x))).
 unfold states at 1.  
 simpl; simpl in rwt_tmp; fold lift_B_ in rwt_tmp; rewrite rwt_tmp.
 
 apply (lift_B_extensionality_bisim (S_ X) (fun x0=> h (i1 x0)) (fun x0:S_ X=> Beta Lambda (lift_S_ X w.(states) (fun x1 : X => h (i0 x1)) x0))).
 apply (Lam_coiterator_4_11_bisim Lambda (Build_BS_coalgebroid X X_tr)).  
Defined.

End Lambda_Coiteration_theory.
