Require Import Relations.
Load LTS.


Section Bisimulations.
Variable T : LTS.
Variable R : relation T.
(* Usual definition of strong bisimulation *)
Definition sbsim_rel : Prop := forall (m : wlabel), sym_diagram R (trans m) (trans m) R.

(* Usual definition of weak bisimulation *)
Definition bsim_rel : Prop := forall (m : wlabel), sym_diagram R (trans m) (whtrans m) R.

End Bisimulations.

Arguments sbsim_rel [_] _.
Arguments bsim_rel [_] _.


Section Bisimilarities.
Variable T : LTS.

(* Strong bisimilarity as the largest strong bisimulation relation *)
Definition sbsim (x y : T) := exists (R : relation T), R x y /\ sbsim_rel R.
(* Weak bisimilarity as the largest weak bisimulation relation *)
Definition bsim (x y : T)  := exists (R : relation T), R x y /\ bsim_rel R.

(* Some very basic properties of weak bisimilarity*)
Lemma bsim_diag : forall x y, bsim x y -> forall (m : wlabel) x', (x [m] x' -> exists y', (y [* m *] y' /\ bsim x' y')).
intros x y b m x' h.
destruct b as [R b].
destruct b as [r b].
destruct (b m) as [d d'].
destruct (d x y x' r h) as [y' h'].
exists y'. split; [apply h'|].
exists R; split; [apply h'|assumption].
Qed.

Lemma bsim_diag2 : forall x y, bsim x y -> forall (m : wlabel) y', (y [m] y' -> exists x', (x [* m *] x' /\ bsim x' y')).
intros x y b m y' h.
destruct b as [R b].
destruct b as [r b].
destruct (b m) as [d d'].
destruct (d' y x y' r h) as [x' h'].
exists x'. split; [apply h'|].
exists R; split; [apply h'|assumption].
Qed.

Lemma bsim_bsim: bsim_rel bsim.
intro m; split; intros x y z b t; [eapply bsim_diag|eapply bsim_diag2]; eassumption.
Qed.

End Bisimilarities.

Arguments bsim [_] _ _.
Arguments sbsim [_] _ _.

Infix "~~" := bsim (at level 10).



(* More properties of weak bisimilarity (reflexivity, symmetry, transitivity) *)
Section bsim_prop.
Variable T:LTS.

Lemma sym_rel : forall (R : relation T), bsim_rel R <-> bsim_rel (transp T R).
intro R. split; intros h m; destruct h with m as [h' h'']; split; assumption.
Qed.

Lemma sym_bsim : forall (x y : T), x ~~ y <-> y ~~ x.
intros x y. split; intros h; destruct h as [R h]; destruct h as [h h']; exists (transp T R); 
  split; try (apply sym_rel); unfold transp; assumption.
Qed.

Lemma refl_bsim : forall x : T, x ~~ x.
assert (bsim_rel (fun (x y : T) => x = y)).
+ intros m. split; intros x y z eq tr; exists z; split; try trivial; induction m; simpl; subst.
- apply rt_step. trivial.
- exists y; split; [apply rt_refl|exists z; split; [|apply rt_refl] ]; trivial.
- apply rt_step. unfold transp in eq. subst;  trivial.
- exists y. unfold transp in eq; subst. split; [apply rt_refl| exists z; split; [|apply rt_refl] ]; trivial.
- unfold transp; trivial.
- unfold transp; trivial.
+ intro x. exists (fun x y : T => x = y). auto.
Qed.


Lemma bsim_diag_wttransl : forall (R : relation T), bsim_rel R -> diagram R (fun (x y :T) => wttrans x y) (fun (x y :T) => wttrans x y) R.
intros R br.
destruct (br t) as [diag rdiag]; simpl in *. unfold wttrans in *.
eapply equiv_diag. apply rel_eq_eq. apply rel_eq_eq. apply rel_eq_fun.  apply trans_refl_trans_refl_eq2. 
apply rel_eq_eq. apply (diag_comp_rt T R (trans t) (clos_refl_trans T (trans t)) diag).
Qed.

Lemma bsim_diag_wttransr : forall (R : relation T), bsim_rel R -> rev_diagram R (fun (x y :T) => wttrans x y) (fun (x y :T) => wttrans x y) R.
intros R br.
destruct (br t) as [diag rdiag]; simpl in *. unfold wttrans in *.
unfold rev_diagram. apply bsim_diag_wttransl. apply (sym_rel R). apply br.
Qed.

Lemma comp_tau_weak : forall m, rel_eq T (wtrans m) (rel_comp T (wtrans m) (fun x y:T => x >*y)).
intros m. intros x y . split; intros tr.
+ exists y. split; [apply tr|apply rt_refl].
+ destruct tr as [x'' s]; destruct s as [tr ttr'].
  destruct tr as [x' s]. destruct s as [ttr s].
  destruct s as [z s]. destruct s as [tr' ttr''].
  exists x'. split; [apply ttr|].
  exists z. split; [apply tr'|].
  apply trans_trans_refl_eq2.
  apply t_trans with x''; apply t_step; assumption.
Qed.

Lemma comp_tau_weak2 : forall m, rel_eq T (rel_comp T (fun x y:T => x >*y) (wtrans m)) (wtrans m).
intros m. intros x y . split; intros tr.
+ destruct tr as [x'' s]; destruct s as [ttr' tr].
  destruct tr as [x' s]. destruct s as [ttr s].
  destruct s as [z s]. destruct s as [tr' ttr''].
  exists x'. split; [|].
  -   apply trans_trans_refl_eq2.   apply t_trans with x''; apply t_step; assumption.
  - exists z. split; [apply tr'|]. assumption.
+ exists x. split; [apply rt_refl|assumption].
Qed.

Lemma bsim_diag_weakl : forall (R : relation T) a, bsim_rel R -> diagram R (wtrans (l a)) (wtrans (l a)) R.
intros R a br.
eapply equiv_diag with R _ (rel_comp T (fun x y:T=> x>*y) (wtrans (l a))) R; try apply rel_eq_eq.
  - apply comp_tau_weak2.
  - apply diag_compose with R.
    * apply bsim_diag_wttransl. apply br.
    * eapply equiv_diag with R _ (rel_comp T (wtrans (l a)) (fun x y:T => x>*y)) R; try apply rel_eq_eq.
      + apply rel_eq_sym. apply comp_tau_weak.
      + apply diag_compose with R. apply br. apply bsim_diag_wttransl. apply br.
Qed.

Lemma bsim_diag_hweakl : forall (R : relation T) m, bsim_rel R -> diagram R (whtrans m) (whtrans m) R.
intros R m br. induction m.
+ simpl. apply bsim_diag_wttransl. apply br.
+ simpl. apply bsim_diag_weakl. apply br.
Qed.

Lemma bsim_diag_weak : forall (x y : T) x' m, x ~~ y -> x [*m*] x' -> exists y', y [*m*] y' /\ x' ~~ y'.
intros x y x' m b tr.
+ edestruct bsim_diag_hweakl.
  - apply bsim_bsim.
  - apply b.
  - apply tr.
  - exists x0. assumption.
Qed.


Lemma bsim_rel_trans : forall R R': relation T, bsim_rel R -> bsim_rel R' -> bsim_rel (rel_comp T R R').
intros R R' br br' m. split.
+ intros x y z rc tr.
  destruct rc as [w s]; destruct s as [r r'].
  destruct br with m as [d _]. destruct d with x w z as [w' s]; try assumption.
  destruct s as [trw rw].
  destruct bsim_diag_hweakl with R' m w y w' as [y' s]; try assumption.
  destruct s as [try r'y'].
  exists y'. split; [assumption| exists w'] ; split; assumption.
+ intros x y z rc tr.
  unfold transp in rc.
  destruct rc as [w s]; destruct s as [r r'].
  destruct br' with m as [_ d]. destruct d with x w z as [w' s]; try assumption.
  destruct s as [trw rw].
  destruct bsim_diag_hweakl with (transp T R) m w y w' as [y' s]; try assumption; try apply sym_rel; try assumption.
  destruct s as [try r'y'].
  exists y'. split; [assumption| exists w'] ; split; assumption.
Qed.
  

Lemma bsim_trans: forall (x y z : T), x ~~ y -> y ~~ z -> x ~~ z.
intros x y z h h'.
destruct h as [R s]; destruct h' as [R' s'].
exists (rel_comp T R R').
split; [|apply bsim_rel_trans; [apply s|apply s'] ].
exists y. split; [apply s| apply s'].
Qed.




End bsim_prop.

(* transitive closures of relations and relations over functions (for autonomous transitions and operators) *)

Lemma rel_fall : forall (A : Type) (R: relation A) (f g : A -> A),
clos_refl_trans (A -> A) (fun h h' => forall (x : A), R (h x) (h' x)) f g -> forall x, (clos_refl_trans A R) (f x) (g x).
intros.
induction H.
constructor. apply H.
apply rt_refl.
eapply rt_trans;
eassumption.
Qed.

Arguments sym_rel [_] _.
Arguments sym_bsim [_] _ _.



Lemma clos_refl_trans_one_or : forall (A : Type) (R : relation A) (x y : A), clos_refl_trans A R x y
-> (x = y) \/ (exists z, R x z /\ clos_refl_trans A R z y).
intros A R x y h.
induction h as [ x y r| | ].
+ right. exists y. split; [assumption|apply rt_refl].
+ left; trivial.
+ destruct IHh1; subst; [destruct IHh2; subst|].
  - left; trivial.
  - right. apply H.
  - destruct H as [z' h].
    right. exists z'. split; [apply h|].
    eapply rt_trans. apply h. apply h2.
Qed.


