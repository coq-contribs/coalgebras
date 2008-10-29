(************************************************************************)
(* Copyright 2008 Milad Niqui                                           *)
(* This file is distributed under the terms of the                      *)
(* GNU Lesser General Public License Version 3                          *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses/lgpl.txt>              *)
(************************************************************************)

Require Export Bisimulation.

(** Module type for weakly final coalgebars. *)

Module Type Weakly_Final_Coalgebra.

Include Type Bisimulation_For_Coalgebra.

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

End Weakly_Final_Coalgebra_theory.