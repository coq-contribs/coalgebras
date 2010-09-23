(************************************************************************)
(* Copyright 2008-2010 Milad Niqui                                      *)
(* This file is distributed under the terms of the                      *)
(* GNU Lesser General Public License Version 3                          *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses/lgpl-3.0.html>         *)
(************************************************************************)

Require Export WeaklyFinalCoalgebra.

(** Formalisation of the Lambda-coiteration definition scheme [1].

[1] Falk Bartels. On Generalised Coinduction and Probabilistic specification Formats:
   Distributive laws in coalgebraic modelling. PhD thesis, VU Amsterdam, 2004.

Note on nomenclature: [T], [T_iter j] and [T_star] are originally denoted by S, S^j and H in [1].

*)


Module Lambda_Coiteration_theory (MB:Weakly_Final_Coalgebra) (MT:Set_Functor).

Import MB MT.
Export MB MT.

Module MB_Weakly_Final_Coalgebra_Theory := Weakly_Final_Coalgebra_theory MB.

Definition B_:=MB.F_.
Definition lift_B_id:=MB.lift_F_id.
Definition lift_B_compose:=MB.lift_F_compose.
Definition lift_B_:=MB.lift_F_.
Definition lift_B_extensionality:=MB.lift_F_extensionality.
Definition B_coalgebra_compose:=MB_Weakly_Final_Coalgebra_Theory.F_coalgebra_compose.
Definition rel_image_lift_B_:=MB.rel_image_lift_F_.
Definition lift_B_extensionality_bisim:=MB.lift_F_extensionality_bisim.
Definition image_span_is_F_bisimulation_strong:=MB_Weakly_Final_Coalgebra_Theory.image_span_is_F_bisimulation_strong.
Definition B_unfold_morphism:=MB_Weakly_Final_Coalgebra_Theory.F_unfold_morphism.
Definition B_coalgebra:=MB.F_coalgebra.


Module MT_Functor_Iter_Theory := Set_Functor_Iter_theory MT.

Definition T_:=MT.F_.
Definition lift_T_:=MT.lift_F_.
Definition lift_T_id:=MT.lift_F_id.
Definition lift_T_compose:=MT.lift_F_compose.
Definition lift_T_extensionality:=MT.lift_F_extensionality.
Definition T_iter := MT_Functor_Iter_Theory.F_iter.
Definition lift_T_iter := MT_Functor_Iter_Theory.lift_F_iter.
Definition T_iter_S :=  MT_Functor_Iter_Theory.F_iter_S.
Definition lift_T_iter_extensionality := MT_Functor_Iter_Theory.lift_F_iter_extensionality.
Definition lift_T_iter_id := MT_Functor_Iter_Theory.lift_F_iter_id.
Definition lift_T_iter_compose := MT_Functor_Iter_Theory.lift_F_iter_compose.

Let T_star_ (X:Set) := { j:nat & (T_iter j X) }.

Let lift_T_star_ (X Y:Set) (f:X->Y) (hx: T_star_ X) : T_star_ Y := let (j, s_ix) := hx in existT _ j (lift_T_iter _ _ f j s_ix).

Let lift_T_star_id :forall X (fx: T_star_ X), fx = lift_T_star_ X X (fun x0 : X => x0) fx.
Proof.
 intros X [j x0]; simpl; assert (hyp0:=lift_T_iter_id X j x0); fold lift_T_iter in hyp0; rewrite <- hyp0; trivial.
Defined.

Let lift_T_star_compose (X Y Z:Set) (g:X->Y) (f:Y->Z) hx: 
   (fun hx0 => lift_T_star_ Y Z f (lift_T_star_ X Y g hx0)) hx = lift_T_star_ X Z (fun x => f (g x)) hx.
Proof.
 destruct hx as [j x0]; simpl; rewrite lift_T_iter_compose; trivial.
Defined.

Let lift_T_star_extensionality: forall (X Y:Set) (f0 f1:X->Y) hx, (forall x, f0 x = f1 x) -> lift_T_star_  _ _ f0 hx = lift_T_star_ _ _ f1 hx.
Proof.
 intros X Y f0 f1 [j x0] hyp_ext;
 simpl.
 f_equal.
 apply lift_T_iter_extensionality; trivial.
Defined.


Let T_star_coproject_ (X:Set) (j:nat) (x: T_iter j X) : T_star_ X := existT _ j x.

Let infinite_case_analysis (X Y:Set) (fs:forall j:nat, T_iter j X -> Y)  (h:T_star_ X) : Y := 
    let (i,x):= h in fs i x.

(* Note that this is not a coalgebra in the sense of Set_Coalgebra,
because we do not require BT to be a Set_Fucntor. *)

Record BT_coalgebroid : Type := 
{ bs_states : Set 
; bs_transition: bs_states -> B_ (T_ bs_states) 
}.

Record T_over_B_distributive : Type :=
{ lambda_ : forall (X:Set) , T_ (B_ X) -> B_ (T_ X)
; lambda_is_natural_: forall (X Y:Set) (f:X->Y) (sbx:T_ (B_ X)), 
     lambda_ _ (lift_T_ _ _ (lift_B_ _ _ f) sbx) = lift_B_ (T_ X) (T_ Y) (lift_T_ _ _ f) (lambda_ _ sbx)
}.

Fixpoint lambda_iter_ (Lambda : T_over_B_distributive) (j : nat) (X:Set) {struct j} :
         T_iter j (B_ X) -> B_ (T_iter j X) :=
         match Lambda with
         | Build_T_over_B_distributive lam_ n_ =>
             match j
             with
             | O => fun (x : B_ X) => x
             | S j' => fun (s_ix : T_iter j' (T_ (B_ X))) =>
                 lambda_iter_ (Build_T_over_B_distributive lam_ n_) j' (T_ X) (lift_T_iter (T_ (B_ X)) (B_ (T_ X)) (lam_ X) j' s_ix)
             end
         end.

Let lambda_star (Lambda:T_over_B_distributive) (X:Set) : T_star_ (B_ X) -> B_ (T_star_ X) :=
   infinite_case_analysis _ _ (fun j s_ibx => lift_B_ _ _ (T_star_coproject_ X j) (lambda_iter_ Lambda j X s_ibx)).

Let Chi (X:Set) : T_star_ (T_ X) -> (T_star_ X) := infinite_case_analysis _ _ (fun j => T_star_coproject_ X (S j)).

Definition Lam_coiterator (Lambda:T_over_B_distributive) (BS: BT_coalgebroid) : BS.(bs_states) -> w.(states) :=
   match BS with
   | Build_BT_coalgebroid X X_tr =>
     let i0 := T_star_coproject_ X 0 in
       let T_star_phi := lift_T_star_ _ _ X_tr in
         let lambda_star_SX := lambda_star Lambda (T_ X) in
           let B_Chi_X := lift_B_ _ _ (Chi X) in
             let h := F_unfold (Build_F_coalgebra (T_star_ X) (fun x=> B_Chi_X (lambda_star_SX (T_star_phi x)))) in
             fun x => h (i0 x)
   end.


Definition Beta (Lambda:T_over_B_distributive) : T_ w.(states) -> w.(states):=
       match Lambda with
       | Build_T_over_B_distributive lam_ _=>
           F_unfold (Build_F_coalgebra _ (fun s_bx=> lam_ _ (lift_T_ _ _ (transition w) s_bx)))
       end.

Fixpoint reformat_T_iter_T_right (j : nat) (X:Set) : T_iter (S j) X -> T_ (T_iter j X) :=
  match j 
  with
  | O =>  fun sx => sx
  | S j' =>  reformat_T_iter_T_right j' (T_ X)
  end.

Let bracket_T_j_fun  X j x0 := lift_T_ _ _ (T_star_coproject_ X j) (reformat_T_iter_T_right j _ x0).

Let reformat_T_iter_T_right_property:forall (j:nat) (X Y:Set) (f:X->Y) (ssx:T_iter (S j) X),
   lift_T_ _ _ (lift_T_iter _ _ f j) (reformat_T_iter_T_right j X ssx) = reformat_T_iter_T_right j Y (lift_T_iter X Y f (S j) ssx).
Proof.
 induction j; intros X Y f ssx; trivial.
 stepr (reformat_T_iter_T_right j (T_ Y) (lift_T_iter _ _ (lift_T_ _ _ f) (S j) ssx)); trivial.
 rewrite <- IHj; trivial.
Defined.

Let T_iter_lambda_iter: forall (Lambda:T_over_B_distributive) (j : nat) (X:Set) (sbx:T_iter (S j) (B_ X)), 
   lift_B_ _ _ (reformat_T_iter_T_right j X) (lambda_iter_ Lambda (S j) X sbx) =
   Lambda.(lambda_) (T_iter j X) (lift_T_ _ _ (lambda_iter_ Lambda j X) (reformat_T_iter_T_right j (B_ X) sbx)).
Proof.
 intros [lam nat_lam]; induction j. 
  intros X sbx.

  transitivity (lift_B_ (T_ X) (T_ X) (lift_T_ X X (fun x : X => x)) (lam X sbx)).
   simpl.
   apply lift_B_extensionality; apply lift_T_id.
   transitivity (lam X (lift_T_ (B_ X) (B_ X) (lift_B_ X X (fun x : X => x)) sbx)).
    rewrite nat_lam; trivial.
    assert (eq_ext:lift_T_ (B_ X) (B_ X) (lift_B_ X X (fun x : X => x)) sbx =
                   lift_T_ (B_ X) (B_ X) (fun x : B_ X => x) sbx).
     apply lift_T_extensionality.
     intros bx; symmetry; apply lift_B_id.
     rewrite eq_ext; trivial.

  intros X sbx.
  stepl (lift_B_ _ _ (reformat_T_iter_T_right j (T_ X)) 
                (lambda_iter_ (Build_T_over_B_distributive lam nat_lam) (S j) (T_ X) (lift_T_iter _ _ (lam X) (S j) sbx))); trivial.
  rewrite IHj.
  rewrite <- reformat_T_iter_T_right_property.
  rewrite lift_T_compose.
  trivial.
Defined.


Let Lam_coiterator_4_2_2_naturality_right: forall (Lambda:T_over_B_distributive) X (hsbx:T_star_ (T_ (B_ X))), 
   Lambda.(lambda_) _ (lift_T_ _ _ (lambda_star Lambda X) (infinite_case_analysis _ (T_ (T_star_ (B_ X))) (bracket_T_j_fun _) hsbx)) =
   lift_B_ _ (T_ (T_star_ X)) (infinite_case_analysis _ (T_ (T_star_ X)) (bracket_T_j_fun X)) (lambda_star Lambda _ (lift_T_star_ _ _ (Lambda.(lambda_) X) hsbx)).
Proof.
 intros [lam nat_lam] X hsbx.
 simpl.
 unfold T_star_ in hsbx.
 destruct hsbx as [j sbx].
 simpl.
 rewrite lift_B_compose.
 simpl.
 stepl (lift_B_ _ (T_ (T_star_ X)) (fun x : T_iter j (T_ X) => bracket_T_j_fun X j x) (lambda_iter_ (Build_T_over_B_distributive lam nat_lam) (S j) _ sbx)); trivial.
 unfold bracket_T_j_fun.
 rewrite lift_T_compose. 
 stepr (lam _  (lift_T_ _ _ (fun sjbx0: T_iter j (B_ X) => lift_B_ _ _ (T_star_coproject_ X j) (lambda_iter_ (Build_T_over_B_distributive lam nat_lam) j X sjbx0))  (reformat_T_iter_T_right j (B_ X) sbx))); trivial.
 rewrite <- lift_T_compose with (Y:=B_ (T_iter j X)).
 rewrite (nat_lam (T_iter j X) _ (T_star_coproject_ X j)).
 simpl.
 assert (lambda_iter_j_property:=T_iter_lambda_iter (Build_T_over_B_distributive lam nat_lam) j X sbx).
 simpl in lambda_iter_j_property.
 fold lift_T_.
 rewrite <- lambda_iter_j_property.
 rewrite lift_B_compose.
 trivial.
Defined.


Let Lam_coiterator_4_2_2_naturality_left: forall (Lambda:T_over_B_distributive) X (hsbx:T_star_ (T_ (B_ X))),
    lift_B_ _ _ (Chi X) (lambda_star Lambda (T_ X) (lift_T_star_ _ _ (Lambda.(lambda_) X) hsbx)) =
    lambda_star Lambda X (Chi (B_ X) hsbx).
Proof.
 intros [lam nat_lam] X hsbx.
 simpl. 
 unfold T_star_ in hsbx.
 destruct hsbx as [j sbx].
 stepl (   lift_B_ (T_star_ (T_ X)) (T_star_ X) (Chi X)
     (lift_B_ (T_iter j (T_ X)) (T_star_ (T_ X)) (T_star_coproject_ (T_ X) j)
        (lambda_iter_ (Build_T_over_B_distributive lam nat_lam) (S j) X sbx))); trivial.
 stepr  ( lambda_star (Build_T_over_B_distributive lam nat_lam) X
     (Chi (B_ X) (T_star_coproject_ (T_ (B_ X)) j sbx))); trivial.
 rewrite lift_B_compose.
 trivial.
Defined.
 
Let Lam_coiterator_4_11_bisim : forall (Lambda:T_over_B_distributive) (BS: BT_coalgebroid) (x:T_ BS.(bs_states)),
   let X:=BS.(bs_states) in
    let X_tr := BS.(bs_transition) in
     let i1 := T_star_coproject_ X 1 in
       let T_star_phi := lift_T_star_ _ _ X_tr in
         let lambda_star_SX := lambda_star Lambda (T_ X) in
           let B_Chi_X := lift_B_ _ _ (Chi X) in
             let h := F_unfold (Build_F_coalgebra (T_star_ X) (fun x=> B_Chi_X (lambda_star_SX (T_star_phi x)))) in
               h (i1 x) (=) (Beta Lambda) (lift_T_ _ _ (Lam_coiterator Lambda (Build_BT_coalgebroid X X_tr)) x).
Proof.
 intros Lambda [X X_tr] sx.
 unfold bs_states.
 unfold bs_states in sx.
 unfold bs_transition.
 set (h := F_unfold (Build_F_coalgebra (T_star_ X) (fun x=> 
         lift_B_ (T_star_ (T_ X)) (T_star_ X) (Chi X)
           (lambda_star Lambda (T_ X) (lift_T_star_ X (B_ (T_ X)) X_tr x))))).
 simpl in h.

 (* 1 *)
 assert (triangle1: lift_T_ _ _ (Lam_coiterator Lambda (Build_BT_coalgebroid X X_tr)) sx=
                    lift_T_ _ _ h (lift_T_ _ _ (T_star_coproject_ X 0) sx));
 [ rewrite (lift_T_compose); trivial |].
 unfold bs_states in triangle1. 
 rewrite triangle1.

 unfold T_iter.
 set (bracket_T_j:= bracket_T_j_fun X).
 (* 2 *)
 assert (triangle2:lift_T_ X (T_star_ X) (T_star_coproject_ X 0) sx=
                   infinite_case_analysis (T_ X) (T_ (T_star_ X)) bracket_T_j (T_star_coproject_ (T_ X) 0 sx));
 trivial.
 simpl; rewrite triangle2.
 (* 3 *)
 assert (triangle3: T_star_coproject_ X 1 sx=Chi X (T_star_coproject_ (T_ X) 0 sx)); trivial.
 rewrite triangle3.
 set (F1:=fun hsx => h (Chi X hsx)).
 set (F2:=fun hsx => Beta Lambda (lift_T_ _ _ h  (infinite_case_analysis (T_ X) (T_ (T_star_ X)) bracket_T_j hsx))).
 change (F1 (T_star_coproject_ (T_ X) 0 sx)(=)F2 (T_star_coproject_ (T_ X) 0 sx)).
 destruct Lambda as [lam nat_lam]. 
  set (psi:=fun sx0 => lam (T_ X) ((lift_T_ _ _ X_tr) sx0)).
  set (alpha_psi:= fun hsx => 
           lift_B_ _ _ (Chi (T_ X)) (lambda_star (Build_T_over_B_distributive lam nat_lam) _ (lift_T_star_ _ _ psi hsx))).  
  set (HSX_as_coalgebra:=Build_F_coalgebra (T_star_ (T_ X)) alpha_psi).
  set (alpha_phi:=fun x=> lift_B_ _ _ (Chi X) ((lambda_star (Build_T_over_B_distributive lam nat_lam) (T_ X)) (lift_T_star_ _ _ X_tr x))).
  set (HX_as_coalgebra:=Build_F_coalgebra (T_star_ X) alpha_phi).
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
     assert (triangle4:lift_T_star_ _ _ (lam (T_ X)) (lift_T_star_ _ _ (lift_T_ _ _ X_tr) s0)=
                       (lift_T_star_ (T_ X) (B_ (T_ (T_ X))) psi s0)).
     rewrite lift_T_star_compose; trivial.

     fold T_; rewrite <- triangle4.
     (* 5 *)
     assert (square5:lift_T_star_ X (B_ (T_ X)) X_tr (Chi X s0)=Chi (B_ (T_ X)) (lift_T_star_ _ _ (lift_T_ _ _ X_tr) s0)).
     destruct s0 as [j sx_]; trivial.

     rewrite square5.
     rewrite Lam_coiterator_4_2_2_naturality_left; trivial.
    unfold F1.  
    apply (B_coalgebra_compose HSX_as_coalgebra HX_as_coalgebra w);[exact Chi_X_is_coalgebra_map|exact h_is_coalgebra_map].
   (* upper route is a coalgebra map *)
    set (alpha_sigma:=fun x=> lam _ (lift_T_ _ _ alpha_phi x)).
    set (SHX_as_coalgebra := Build_F_coalgebra (T_ (T_star_ X)) alpha_sigma).
    set (alpha_omega:=fun x=> lam _ (lift_T_ _ _ w.(transition) x)).
    set (T_Str_as_coalgebra := Build_F_coalgebra (T_ w.(states)) alpha_omega).
    unfold F2; intros hsx.

    rewrite (B_coalgebra_compose HSX_as_coalgebra SHX_as_coalgebra w (infinite_case_analysis (T_ X) (T_ (T_star_ X)) bracket_T_j) 
                   (fun shx => (Beta (Build_T_over_B_distributive lam nat_lam) (lift_T_ (T_star_ X) w.(states) h shx)))     ); trivial.

     clear hsx; intros hsx.
     simpl.
     unfold alpha_psi.
     (* 6 *)
     assert (triangle4:lift_T_star_ _ _ (lam (T_ X)) (lift_T_star_ _ _ (lift_T_ _ _ X_tr) hsx)=
                       (lift_T_star_ (T_ X) (B_ (T_ (T_ X))) psi hsx)).
     rewrite lift_T_star_compose; trivial.

     fold T_; rewrite <- triangle4.
     (* 7 *) 
     assert (square7:forall hssx, infinite_case_analysis (T_ X) (T_ (T_star_ X)) bracket_T_j (Chi (T_ X) hssx) =
                                 lift_T_ _ _ (Chi X) (infinite_case_analysis _ _ (bracket_T_j_fun (T_ X)) hssx)).
     intros [j ssx]; unfold bracket_T_j_fun; simpl; rewrite lift_T_compose; trivial.

     rewrite (lift_B_compose).  
     fold T_.
     set (bx:=(lambda_star (Build_T_over_B_distributive lam nat_lam)  (T_ (T_ X))
                 (lift_T_star_ _ _ (lam (T_ X)) (lift_T_star_ (T_ X) (T_ (B_ (T_ X))) (lift_T_ X (B_ (T_ X)) X_tr) hsx)))).
     rewrite (lift_B_extensionality _ (T_ (T_star_ X)) (fun hssx=> infinite_case_analysis (T_ X) (T_ (T_star_ X)) bracket_T_j (Chi (T_ X) hssx))
                           (fun hssx => lift_T_ _ _ (Chi X) (infinite_case_analysis _ (T_ (T_star_ (T_ X))) (bracket_T_j_fun _) hssx)) bx square7).
     rewrite <- lift_B_compose with (Y:=T_ (T_star_ (T_ X))).
     subst bx.
     rewrite <- Lam_coiterator_4_2_2_naturality_right.
     unfold alpha_sigma, alpha_phi.
     rewrite <- lift_T_compose with (Y:=B_ (T_star_ (T_ X))).
     rewrite <- lift_T_compose with (Y:=T_star_ (B_ (T_ X))).
     (* 8 *)
     assert (square8:lift_T_ _ _ (lift_T_star_ X (B_ (T_ X)) X_tr) (infinite_case_analysis _ _ bracket_T_j hsx)=
                     infinite_case_analysis _ _ (bracket_T_j_fun (B_ (T_ X))) (lift_T_star_ _ _ (lift_T_ X (B_ (T_ X)) X_tr) hsx)).
      clear sx triangle1 triangle2 triangle3; destruct hsx as [j sx].
      unfold bracket_T_j, bracket_T_j_fun; simpl.
      assert (square8_1:forall ssx,lift_T_ (T_star_ X) (T_star_ (B_ (T_ X))) (lift_T_star_ X (B_ (T_ X)) X_tr) (lift_T_ _ _ (T_star_coproject_ X j) ssx) =
                                  lift_T_ _ _ (T_star_coproject_ (B_ (T_ X)) j) (lift_T_ _ _ (lift_T_iter _ _ X_tr j) ssx)).
      intros ssx; do 2 rewrite lift_T_compose; apply lift_T_extensionality; trivial.

      rewrite square8_1.
      rewrite reformat_T_iter_T_right_property; trivial.

     fold lift_T_; fold T_ in square8; rewrite square8.
     rewrite (nat_lam _ _ (Chi X)); trivial.

    intros shx; 
    rewrite (B_coalgebra_compose SHX_as_coalgebra T_Str_as_coalgebra w (lift_T_ _ _ h) (Beta (Build_T_over_B_distributive lam nat_lam))); trivial;  clear shx hsx.

     intros shx.
     unfold T_Str_as_coalgebra, SHX_as_coalgebra, alpha_omega, alpha_sigma, transition at 2.
     rewrite lift_T_compose.
     assert  (T_lifts_h_finality:forall shx, lift_T_ _ _ (fun hx => transition w (h hx)) shx= 
                                             lift_T_ _ _ (fun hx=>lift_B_ _ _ h (alpha_phi hx)) shx).
      clear shx; intros shx; apply lift_T_extensionality; apply (commutativity_F_unfold HX_as_coalgebra).
     rewrite T_lifts_h_finality.
     rewrite <- lift_T_compose with (Y:=B_ (T_star_ X)).

     assert (rwt_tmp:=nat_lam (T_star_ X) w.(states) h (lift_T_ _ (B_ (T_star_ X)) alpha_phi shx)).
     fold lift_T_ T_ B_; fold B_ in rwt_tmp. 
     rewrite rwt_tmp.
     trivial.

     intros sstr; apply commutativity_F_unfold.
Defined.


Lemma commutativity_Lam_coiterator_rel_image_lifting (Lambda:T_over_B_distributive) (BS: BT_coalgebroid) (x:BS.(bs_states)) : 
rel_image_lift_B_ w w bisimilar (w.(transition) (Lam_coiterator Lambda BS x))
         ( lift_B_ _ _ (Beta Lambda) (lift_B_ _ _  (lift_T_ _ _ (Lam_coiterator Lambda BS)) (bs_transition BS x))).
Proof.
 destruct BS as [X X_tr].
 unfold Lam_coiterator.
 rewrite (commutativity_F_unfold
(Build_F_coalgebra (T_star_ X)
           (fun x0 : T_star_ X =>
            lift_B_ (T_star_ (T_ X)) (T_star_ X) (Chi X)
              (lambda_star Lambda (T_ X) (lift_T_star_ X (B_ (T_ X)) X_tr x0)))) (T_star_coproject_ X 0 x)).
 set (i0:=T_star_coproject_ X 0).
 set (i1:=T_star_coproject_ X 1).
 set (T_star_phi:=lift_T_star_ _ _ X_tr).
 set (lambda_star_SX := lambda_star Lambda (T_ X)).
 set (B_Chi_X := lift_B_ _ _ (Chi X)).
 set (h := F_unfold (Build_F_coalgebra (T_star_ X) (fun x=> B_Chi_X (lambda_star_SX (T_star_phi x))))).
 unfold transition, bs_transition, bs_states.
 assert (rwt_tmp:=lift_B_compose _ _ _ (lift_T_ _ _  (fun x0 : X => h (i0 x0))) (Beta Lambda) (X_tr x)).
 fold T_ lift_B_; fold T_ lift_B_ in rwt_tmp; 
 rewrite rwt_tmp.

 (* square 1 *)
 assert (square1:(T_star_coproject_  (B_ (T_ X)) 0 ) (X_tr x) = T_star_phi (i0 x)); trivial.
 rewrite <- square1.
 (* triangle 2 *)
 assert (triangle2:(lift_B_ _ _ (T_star_coproject_  (T_ X) 0 )) (X_tr x) = (lambda_star_SX (T_star_coproject_ (B_ (T_ X)) 0 (X_tr x)))); [destruct Lambda; trivial|].
 rewrite <- triangle2.
 (* triangle 3 *)
 assert (triangle3:(lift_B_ _ _ (T_star_coproject_ X 1) (X_tr x))=B_Chi_X (lift_B_ _ _ (T_star_coproject_ (T_ X) 0) (X_tr x)));
 [unfold B_Chi_X; rewrite lift_B_compose; apply lift_B_extensionality; trivial|].
 rewrite <- triangle3.
 unfold T_iter.
 clear rwt_tmp. assert (rwt_tmp:=(lift_B_compose _ _ _ (T_star_coproject_ X 1) h (X_tr x))).
 unfold states at 1.  
 simpl; simpl in rwt_tmp; fold lift_B_ in rwt_tmp; rewrite rwt_tmp.
 
 apply (lift_B_extensionality_bisim (T_ X) (fun x0=> h (i1 x0)) (fun x0:T_ X=> Beta Lambda (lift_T_ X w.(states) (fun x1 : X => h (i0 x1)) x0))).
 apply (Lam_coiterator_4_11_bisim Lambda (Build_BT_coalgebroid X X_tr)).  
Defined.

Section setoid_facilities.

Lemma Beta_morphism : forall (Lambda: T_over_B_distributive) (tx ty: T_ w.(states)), 
   (maximal_bisimulation (Build_F_coalgebra _ (fun s_bx=> Lambda.(lambda_) _ (lift_T_ _ _ (transition w) s_bx)))
                         (Build_F_coalgebra _ (fun s_bx=> Lambda.(lambda_) _ (lift_T_ _ _ (transition w) s_bx))) tx ty) ->
   Beta Lambda tx (=) Beta Lambda ty.
Proof.
 intros [lam_ nat_lam] tx ty hyp; unfold Beta; apply B_unfold_morphism; assumption.
Qed.

Add Parametric Morphism (Lambda: T_over_B_distributive) : (Beta Lambda)
 with signature  (maximal_bisimulation (Build_F_coalgebra _ (fun s_bx=> Lambda.(lambda_) _ (lift_T_ _ _ (transition w) s_bx))) 
                                       (Build_F_coalgebra _ (fun s_bx=> Lambda.(lambda_) _ (lift_T_ _ _ (transition w) s_bx)))) ==> 
                 (maximal_bisimulation w w) as Beta_Morphism.
Proof. 
 apply Beta_morphism.
Qed.


End setoid_facilities.


End Lambda_Coiteration_theory.


Module Primitive_Corecursion (MB:Weakly_Final_Coalgebra).

Import MB.
Export MB.

Definition B_:=MB.F_.


(* X |------> X + w *)
Module Weak_fin_coalg_B_Set_module_argument <: Set_module_argument.
Definition U:=w.(states).
End Weak_fin_coalg_B_Set_module_argument.

Module Weak_fin_coalg_as_Set_Functor:= constant_as_Set_Functor Weak_fin_coalg_B_Set_module_argument.

Module Corecursion_Functor:=coproduct_as_Set_Functor identity_as_Set_Functor Weak_fin_coalg_as_Set_Functor.

Module Import Corecursion_LamCoiter := Lambda_Coiteration_theory MB Corecursion_Functor.

Let il (X:Set) (x:X) : T_ X := inl (states w) x.
Let ir (X:Set) (w:w.(states)) : T_ X := inr X w.

Let prim_corec_tupling (X:Set) (f:X->w.(states)) (tx:T_ X) : w.(states) := 
       match tx with 
       | inl x0 => f x0
       | inr w0 => w0
       end.

Definition lambda_corecursion (X:Set) (tbx:T_ (B_ X)) : B_ (T_ X) :=
       match tbx with
       | inl bx => lift_B_ X (T_ X) (il X) bx
       | inr w0 => lift_B_ w.(states) (T_ X) (ir X) (w.(transition) w0)
       end.

Lemma lambda_corecursion_natural: forall (X Y : Set) (f : X -> Y) (sbx : T_ (B_ X)),
    lambda_corecursion Y (lift_T_ (B_ X) (B_ Y) (lift_B_ X Y f) sbx) =  lift_B_ (T_ X) (T_ Y) (lift_T_ X Y f) (lambda_corecursion X sbx).
Proof.
 intros X Y f [bx | w0]; simpl.
 unfold identity_as_Set_Functor.lift_F_; do 2 rewrite lift_B_compose; apply lift_B_extensionality; trivial.
 rewrite lift_B_compose; unfold Weak_fin_coalg_as_Set_Functor.lift_F_; apply lift_B_extensionality; trivial.
Qed.

Definition prim_corec_distributive:= Build_T_over_B_distributive lambda_corecursion lambda_corecursion_natural.

Definition Corecursor:= Lam_coiterator prim_corec_distributive.

Lemma Beta_corecursor_cotupling_id: forall (x: T_ w.(states)), Beta prim_corec_distributive x (=) prim_corec_tupling _ (fun x0 => x0) x.
Proof.
 apply (F_unique (Build_F_coalgebra _ (fun s_bx=> lambda_corecursion _ (lift_T_ _ _ (transition w) s_bx)))). 
  intros x; apply (commutativity_F_unfold _ x). 
  intros [x0 | w0]; simpl; rewrite lift_B_compose; apply lift_B_id.
Qed.

Lemma commutativity_Corecursor_rel_image_lifting (BT: BT_coalgebroid) (x:BT.(bs_states)) : 
rel_image_lift_B_ w w bisimilar (w.(transition) (Corecursor BT x))
        (lift_B_ _ _ (prim_corec_tupling _ (Corecursor BT)) (BT.(bs_transition) x)).
Proof.
 apply MB_Weakly_Final_Coalgebra_Theory.rel_image_bisimilar_transitive  
  with (lift_B_ _ _ 
        (fun x0=> Beta prim_corec_distributive (lift_T_ _ _ (Corecursor BT) x0)) (bs_transition BT x)).
 
  generalize (commutativity_Lam_coiterator_rel_image_lifting prim_corec_distributive BT x).
  fold Corecursor; rewrite lift_B_compose; trivial.

  apply lift_B_extensionality_bisim.
  clear; intros x.
  rewrite Beta_corecursor_cotupling_id.
  destruct x as [x0 | w0]; simpl.
   unfold identity_as_Set_Functor.lift_F_; apply MB_Weakly_Final_Coalgebra_Theory.refl_bisimilar.
   unfold Weak_fin_coalg_as_Set_Functor.lift_F_; apply MB_Weakly_Final_Coalgebra_Theory.refl_bisimilar.
Qed.


End Primitive_Corecursion.