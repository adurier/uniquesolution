Require Import Relations.
Load rels.

Section LTS.
(* Weak labels: either a normal (visible) label or a tau *)
Inductive wlabel (L : Type) : Type :=
 | t : wlabel L
 | l : L -> wlabel L.

(* Labeled Transition System: a base set ('carrier', the struct is coerced to its carrier), a set of (visible) label names,
    and a transition relation over the base for each weak label. *)
Structure LTS : Type := lts {
  carrier : Type;
  label : Type;
  trans : wlabel label -> relation carrier }.

Coercion carrier : LTS >-> Sortclass.

End LTS.

(* Implicit arguments *)
Arguments label [_].
Arguments wlabel [_].
Arguments t [_].
Arguments l [_] _.
Arguments trans [_] _ _ _.

Notation "x  [ μ ] y" := (trans μ x y) (at level 20).
Notation "x ~> y" := (trans t x y) (at level 10).

(* Usual definitions of weak transitions*)
Section wtransitions.
Variable T : LTS.

(* The weak transition => : sequence (may be empty) of -tau-> transitions. *)
Definition wttrans : relation T := clos_refl_trans T (trans t).
(* The weak transition =m=> : the composition of => with a m-transition with => *)
Definition wtrans (m : wlabel) : relation T := (rel_comp T wttrans (rel_comp T (trans m) wttrans)).
(* The weak transition =^m=> : either => if m=tau, or =m=> otherwise *)
Definition whtrans (m : wlabel) : relation T := match m with
 | t => wttrans
 | l a => wtrans (l a)
end.

End wtransitions.


Arguments wttrans [_] _ _.
Arguments wtrans [_] _ _ _.
Arguments whtrans [_] _ _ _.


Notation "x [[ μ ]] y" := (wtrans μ x y) (at level 20).
Notation "x >* y" := (wttrans x y) (at level 20).
Notation "x [* μ *] y" := (whtrans μ x y) (at level 20).
