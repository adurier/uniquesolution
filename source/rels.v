Require Import Relations.

(* Basic definitions and properties for relations, and relation equivalence *)
Definition rel_eq (A : Type) (R R' : relation A):= forall (x y : A), R x y <-> R' x y.

Lemma rel_eq_eq : forall (A :Type) (R : relation A), rel_eq A R R.
intros. intros x y. split; auto.
Qed.



Lemma rel_eq_fun : forall (A : Type) (R R': relation A), rel_eq A R R' -> rel_eq A R (fun x y => R' x y).
intros. intros x y. split;apply H.
Qed.



Definition rel_comp (A : Type) (R R' : relation A) : relation A := fun x y => exists z, R x z /\ R' z y.


Lemma rel_eq_comp : forall (A : Type) (R R' R0 R0' : relation A), rel_eq A R R0 -> rel_eq A R' R0' -> rel_eq A (rel_comp A R R') (rel_comp A R0 R0').
intros A R1 R2 R1' R2' re re'. intros x y. split; intro rc; induction rc as [z s]. 
+ exists z. split; [apply re|apply re']; apply s.
+ exists z. split; [apply re|apply re']; apply s.
Qed.


Lemma rel_eq_sym : forall (A : Type) R R', rel_eq A R R' -> rel_eq A R' R.
intros. intros x y. split; apply H.
Qed.

(* Diagrams over relations: usefull for defining and reasoning about (strong or weak) bisimulations and bisimilarities *)
Section Diagrams.
Variable X : Type.
Variable R : relation X.
Variable T1 : relation X.
Variable T2 : relation X.
Variable R' : relation X.

Definition diagram := forall (x y z : X), R x y -> T1 x z -> exists z', T2 y z' /\ R' z z'.

End Diagrams.



Lemma diag_comp_trans : forall (A : Type) (R T T': relation A), diagram A R T T' R -> diagram A R (clos_trans A T) (clos_trans A T') R.
intros A R T T' diag.
intros x y z r tr.
revert r; revert y.
induction tr as [x z  t|x x' x'']; intros y r.
+ edestruct diag as [z' s]; try eassumption.
  exists z'.
  split; [constructor|]; apply s.
+ destruct (IHtr1 y r) as [y' hy'].
  destruct (IHtr2 y') as [y'' hy'']; [apply hy'|].
  exists y''.
  split; [|apply hy''].
  apply t_trans with y'.
  apply hy'. apply hy''.
Qed.

Lemma diag_comp_rt : forall (A : Type) (R T T': relation A), diagram A R T T' R -> diagram A R (clos_refl_trans A T) (clos_refl_trans A T') R.
intros A R T T' diag.
intros x y z r tr.
revert r; revert y.
induction tr as [x z t| |x x' x'']; intros y r.
+ edestruct diag as [z' s]; try eassumption.
  exists z'.
  split; [constructor|]; apply s.
+ exists y. split; [|assumption]. apply rt_refl.
+ destruct (IHtr1 y r) as [y' hy'].
  destruct (IHtr2 y') as [y'' hy'']; [apply hy'|].
  exists y''.
  split; [|apply hy''].
  apply rt_trans with y'.
  apply hy'. apply hy''.
Qed.

Lemma diag_compose : forall (A : Type) (R T1 T2 R' T1' T2' R'' : relation A),
 diagram A R T1 T2 R' -> diagram A R' T1' T2' R'' 
 -> diagram A R (rel_comp A T1 T1') (rel_comp A T2 T2') R''.
intros A R T1 T2 R' T1' T2' R'' d1 d2.
intros x y z r rc.
destruct rc as [x' s]; destruct s as [t1 t1'].
destruct (d1 x y x' r t1) as [y' s]; destruct s as [t2 r'].
destruct (d2 x' y' z r' t1') as [y'' s]; destruct s as [t2' r''].
exists y''; split; [|apply r''].
exists y'. split; assumption.
Qed. 

Section RevDiagrams.
Variable X : Type.
Variable R : relation X.
Variable T1 : relation X.
Variable T2 : relation X.
Variable R' : relation X.
Definition rev_diagram := diagram X (transp X R) T1 T2 (transp X R').

End RevDiagrams.


Arguments diagram [_] _ _ _ _.
Arguments rev_diagram [_] _ _ _ _.

Section SymDiagrams.
Variable X : Type.
Variable R : relation X.
Variable T1 : relation X.
Variable T2 : relation X.
Variable R' : relation X.
Definition sym_diagram := diagram R T1 T2 R' /\ rev_diagram R T1 T2 R'.
End SymDiagrams.

Arguments sym_diagram [_] _ _ _ _.


(* Basic properties of diagrams and relations closures *)

Lemma equiv_diag : forall (A : Type) (R1 T1 T2 R2 R1' T1' T2' R2' : relation A), rel_eq A R1 R1' -> rel_eq A T1 T1' -> rel_eq A T2 T2' -> rel_eq A R2 R2' -> diagram R1 T1 T2 R2 -> diagram R1' T1' T2' R2'.
intros. intros x y z h h'. destruct (H3 x y z). apply H. apply h. apply H0. apply h'. exists x0. split.
apply H1. apply H4. apply H2. apply H4. Qed.




Lemma trans_trans_eq : forall (A : Type) (R : relation A), rel_eq A (clos_trans A R) (clos_trans A (clos_trans A R)).
intros. intros x y. split; intro h.
+ constructor; assumption.
+ induction h.
  - apply H.
  - eapply t_trans; eassumption.
Qed.


Lemma trans_trans_eq2 : forall (A : Type) (R : relation A), rel_eq A (clos_trans A (clos_trans A R)) (clos_trans A R).
intros. intros x y. split; intro h.
+ induction h.
  - apply H.
  - eapply t_trans; eassumption.
+ constructor; assumption.
Qed.



Lemma trans_trans_refl_eq2 : forall (A : Type) (R : relation A), rel_eq A (clos_trans A (clos_refl_trans A R)) (clos_refl_trans A R).
intros. intros x y. split; intro h.
+ induction h.
  - induction H. constructor; apply H. apply rt_refl. eapply rt_trans. apply IHclos_refl_trans1. apply IHclos_refl_trans2.
  - eapply rt_trans; eassumption. 
+ induction h.
  - constructor. constructor. assumption.
  - apply t_step. apply rt_refl.
  - eapply t_trans; eassumption. 
Qed.

Lemma trans_refl_trans_refl_eq2 : forall (A : Type) (R : relation A), rel_eq A (clos_refl_trans A (clos_refl_trans A R)) (clos_refl_trans A R).
intros. intros x y. split; intro h.
+ induction h.
  - induction H. constructor; apply H. apply rt_refl. eapply rt_trans. apply IHclos_refl_trans1. apply IHclos_refl_trans2.
  - apply rt_refl.
  - eapply rt_trans; eassumption. 
+ induction h.
  - constructor. constructor. assumption.
  - apply rt_step. apply rt_refl.
  - eapply rt_trans; eassumption. 
Qed.


Lemma weaker_refl_trans : forall (A : Type) (R R' : relation A), (forall x y, R x y -> R' x y) -> forall x y, clos_refl_trans A R x y -> clos_refl_trans A R' x y.
intros A R R' h x y h'.
induction h' as [x y h' | | ].
+ constructor. apply (h x y h').
+ eapply rt_refl.
+ eapply rt_trans with y; assumption.
Qed.



