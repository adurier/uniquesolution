Require Import Relations.
Load operators.


Section divergences.
Variable T : LTS.
Variable O : Op T.

(* An operator that diverges right away: it can start an infinite sequence of tau transitions by itself*)
CoInductive top_divergence : (T -> T) -> Prop :=
 | div_step (f : T -> T) : forall g, aut O t f g -> top_divergence g -> top_divergence f.

(* An operator that can diverge later: it can have some visible transitions before divergence *)
Inductive div_path : (T-> T) -> Prop := 
 | utop_div : forall f, top_divergence f -> div_path f
 | uvis_step : forall f, forall g m, aut O m f g -> div_path g -> div_path f.

(* Being a reduct of another operator *)
Inductive reduct : relation (T->T) :=
 | red_self : forall f, reduct f f
 | red_step : forall f g h m, reduct g h -> aut O m f g -> reduct f h.

(* Divergence later is like having a reduct that diverges now *)
Lemma unfold_div : forall f, (div_path f <-> exists g, top_divergence g /\ reduct f g).
intro f; split.
+ intro d; induction d as [g d|f g m a].
  exists g.
  split; [assumption|constructor].
  destruct IHd as [h s]; destruct s as [d' r].
  exists h. split; [assumption|].
  econstructor; eassumption.
+ intro e.
  destruct e as [h s].
  destruct s as [t r].
  induction r. constructor; assumption.
  eapply uvis_step; try eassumption.
  apply (IHr t).
Qed.


(* Divergences of the infinite unfolding of a function: f can produce a tau transition, then if you compose the remainder
    with f it can produce another, etc *)
CoInductive comp_top_div c : (T -> T) -> Prop :=
 | cdstep : forall f g, aut O t (comp f c) g -> comp_top_div c g -> comp_top_div c f.

(* Same thing, only after some visible transitions*)
Inductive comp_div : (T -> T) -> (T -> T) -> Prop :=
 | top_div : forall c f, comp_top_div c f -> comp_div c f
 | vis_step : forall c f g m, aut O m (comp f c) g -> comp_div c g -> comp_div c f.

(* Divergence of (the infinite unfolding of) an operator: alternate composition and tau transitions (after
    alternating between composition and visible transitions for some time *)
Definition op_div f := comp_div f f.

(* Reduct of a finite unfolding of an operator: we alternate, a finite number of times, between compositions with c
    and transitions (visible or not) to obtain f from c.  *)
Inductive comp_red_c : (T -> T) -> relation (T -> T) :=
 | comp_red_self : forall c f, comp_red_c c f f
 | comp_red_step : forall c f g h m, comp_red_c c g h -> aut O m (comp f c) g -> comp_red_c c f h.

(* comp_red c f means 'f is a reduct of a finite unfolding of c' *)
Definition comp_red c f := comp_red_c c c f.

(* As previously, but for infinite unfoldings instead of operators *)
Lemma red_div_aux : forall c f, (comp_div c f <-> exists g, comp_top_div c g /\ comp_red_c c f g).
intros c f; split.
+ intro d; induction d as [c f d|c f g m a d]. (*inversion d; subst. (* induction d as [c g div|].*)*)
  - exists f.
    split; try assumption; constructor.
  - destruct IHd as [h s].
    destruct s as [topd red].
    exists h.
    split; [apply topd|].
    econstructor; eassumption.
+ intro H; destruct H as [g s].
  destruct s as [topd red].
  induction red as [|c f g h m red i a]; [constructor; assumption|].
  eapply vis_step; [eassumption|auto].
Qed.

Lemma red_div : forall f, (op_div f <-> exists g, comp_top_div f g /\ comp_red f g).
intros; apply red_div_aux.
Qed.

(* after a transition and a composition from a reduct of c, we get a reduct of c *)
Lemma comp_red_right : forall c f g h m, comp_red_c c f g -> aut O m (comp g c) h -> comp_red_c c f h.
intros c f g h m cr autr.
unfold comp_red in cr. induction cr. eapply comp_red_step. eapply comp_red_self. eassumption.
eapply comp_red_step. apply IHcr. apply autr. apply H.
Qed.

End divergences.

Arguments top_divergence [_] _.
Arguments div_path [_] _.
Arguments reduct [_] _ _.
Arguments unfold_div [_] _.
Arguments comp_top_div [_] _ _.
Arguments comp_div [_] _ _.
Arguments op_div [_] _.
Arguments comp_red_c [_] _ _ _.
Arguments comp_red [_] _ _.





