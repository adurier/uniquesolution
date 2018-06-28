Require Import Relations.
Load bsim.

(* Extensional equality of functions: f is extensionnaly equal to g if for all x, f x = g x *)
Definition ext_eq (A : Type) (f g : A -> A) : Prop := forall (x : A), f x = g x.
Arguments ext_eq [_] _ _.



Section functions.
Variable T : LTS.

(* Autonomous transitions of a state function (this definition is not complete, as this is not
   with respect to a specific set of state functions. cf. further for the real definition. This is usefull
   to avoid cycles in  the definition of a set of operator *)
Definition autonomous (m : wlabel) : relation (T -> T) := fun f g => forall (x : T), trans m (f x) (g x).
(* Functions must respect weak bisimilarity. We call it the congruence property. *)
Definition congruence : (T -> T) -> Prop := fun f => forall x y, bsim x y -> bsim (f x) (f y).

(* Composition of functions *)
Definition comp {A} (f : A -> A) (g : A -> A) := fun (x : A) => (f (g x)).

(* Finite unfoldings of a function *)
Fixpoint unfolding (f : T -> T) n := match n with
 | 0 => (fun x => x)
 | S p => comp f (unfolding f p)
end.

(* Some basic properties of composition and unfoldings*)
Lemma unfold_right : forall (f : T -> T) n x,  comp f (unfolding f n) x = comp (unfolding f n) f x.
intros f n x. revert f. revert x. induction n; simpl; intros x f; unfold comp; simpl. trivial.
simpl in IHn. unfold comp in IHn; simpl in IHn. rewrite<- (IHn x f). trivial.
Qed.

Lemma comp_assoc : forall (A : Type) (f g h : A -> A), forall x, comp f (comp g h) x = comp (comp f g) h x.
intros A f g h x. unfold comp; simpl. trivial.
Qed.

Lemma ext_eq_comp : forall A (f g f' g': A -> A), ext_eq f f' -> ext_eq g g' -> ext_eq (comp f g) (comp f' g').
intros A f g f' g' e1 e2 x. unfold comp. rewrite (e1 (g x)). rewrite (e2 x). trivial.
Qed.


End functions.

Arguments autonomous [_] _ _ _.
Arguments congruence [_] _.
Arguments unfolding [_] _ _ _.

(* Tactic for solving extensional equalities *)
Ltac ext_step x := 
 match goal with
  H_ext: ext_eq _ _
  |- _ => specialize (H_ext x)
 end.

(* there seems to be a bug when doing directly the rewrite in the previous tactic *)
Ltac force_subst := match goal with H : _ = _
 |-_ => rewrite H in * end.


Ltac ext := intros; intros ?ext_var; repeat ext_step ext_var; repeat force_subst; reflexivity.

(* Basic properties of extensional equality *)
Section extensional_eq_fun.
Variable A : Type.

Lemma ext_refl: forall (h : A -> A), ext_eq h h.
ext. Qed.

Lemma ext_trans : forall f g h : A -> A, ext_eq f g -> ext_eq g h -> ext_eq f h.
intros. ext. Qed.

Lemma ext_sym : forall f g : A -> A, ext_eq f g -> ext_eq g f.
ext. Qed.

End extensional_eq_fun.



(* Congruence is preserved  by composition and unfoldings *)
Lemma comp_cong : forall (T:LTS) (f g : T -> T), congruence f -> congruence g -> congruence (comp f g).
intros T f g h h' x y h''.
apply h. apply h'. apply h''.
Qed.

Lemma unfold_cong: forall (T:LTS) (f: T-> T), congruence f -> forall n, congruence (unfolding f n).
intros T f c n.
induction n; simpl.
+ intros x y. trivial.
+ intros x y h. apply c.
  apply IHn; apply h.
Qed.




(* Definition of a set of operators *)
Section operators.
Variable T : LTS.

(* A state function is guarded/autonomous over O if all its transitions are autonomous transitions towards a state function of O *)
Definition guarded (P: (T->T) -> Prop) f : Prop := 
  P f /\ forall x y m, trans m (f x) y -> exists f', P f' /\ f'(x) = y /\ autonomous m f f'.

(* Set of operators *)
Structure Op := set_oper {
(* The operator predicate: f is in the set of operators O if op O f holds*)
 op : (T -> T) -> Prop;
(* The identity is always an operator *)
 id : op (fun x => x);
(* Closure of a set of operators by composition *)
 clos_comp : forall f g, op f -> op g -> op (comp f g);
(* Operators are congruences *)
 cong : forall f, op f -> congruence f;
(* Composition respects guardedness/autonomy: if g is guarded over O, then fog is guarded over O *)
 leftguard : forall f g, op f -> guarded op g -> guarded op (comp f g);
(* The set of operators needs to be closed by extensional equality. *)
 clos_ext : forall f g, op f -> ext_eq f g -> op g}.

End operators.

Arguments guarded [_] _ _.

Arguments op [_] _ _.

(* Autonomous transitions over a set of operators O *)
Section aut.
Variable T : LTS.
Variable O : Op T.

Definition aut (m : wlabel) : relation (T -> T) := fun f g => op O f /\ op O g /\ forall (x : T), trans m (f x) (g x).

Lemma aut_aut : forall m f f', aut m f f' -> autonomous m f f'.
intros m f f' h. destruct h as [o h]. destruct h as [o' h]. exact h.
Qed.

End aut.

Arguments aut [_] _ _ _.


(* Closure of a relation over functions, with extensional equality instead of standard equality *)
Section fun_relations.
Variable A : Type.

Inductive clos_refl_trans_fun (R: relation (A -> A)) (f: A -> A) : (A->A) -> Prop :=
 | rtf_step g : R f g -> clos_refl_trans_fun R f g
 | rtf_refl g : ext_eq f g -> clos_refl_trans_fun R f g
 | rtf_trans g h :
    clos_refl_trans_fun R f g -> clos_refl_trans_fun R g h -> clos_refl_trans_fun R f h.



Lemma weaker_refl_trans_fun : forall (R R' : relation (A->A)), (forall x y, R x y -> R' x y) -> forall x y, clos_refl_trans_fun R x y -> clos_refl_trans_fun R' x y.
intros R R' h x y h'.
induction h' as [x y h' | x y eq | x y z r1 r1' r2 r2'].
+ constructor. apply (h x y h').
+ eapply rtf_refl; assumption.
+ eapply rtf_trans with y; assumption.
Qed.


End fun_relations.

Arguments clos_refl_trans_fun [_] _ _ _.



Lemma rel_fall_fun : forall (A : Type) (R: relation A) (f g : A -> A),
clos_refl_trans_fun (fun h h' => forall (x : A), R (h x) (h' x)) f g -> forall x, (clos_refl_trans A R) (f x) (g x).
intros.
induction H.
constructor. apply H.
rewrite (H x). apply rt_refl.
eapply rt_trans;
eassumption.
Qed.


(* Weak autonomous transitions over operators *)
Section op_trans.
Variable T:LTS.


(* Weak => transitions: sequence of tau transitions (may be empty) *)
Definition wtaut (O : Op T) : relation (T -> T) := clos_refl_trans_fun (aut O t).
(* Weak =m=> transitions: composition of a =>, a m transition, and another =>*)
Definition waut (O : Op T) (m : wlabel) : relation (T -> T) := (fun x y => exists x' y', wtaut O x x' /\ aut O m x' y' /\ wtaut O y' y).
(* Weak transitions =^m=> : => if m=tau, =m=> otherwise *)
Definition whaut (O : Op T) (m : wlabel) : relation (T -> T) := match m with
 | t => wtaut O
 | l a => waut O (l a)
end.


(* Weaker definitions (the functions do not have to be in a set of operators). *)
Definition wtauto : relation (T -> T) := clos_refl_trans_fun (autonomous t).
Definition wauto (m : wlabel) : relation (T -> T) := (fun x y => exists x' y', wtauto x x' /\ autonomous m x' y' /\ wtauto y' y).
Definition whauto (m : wlabel) : relation (T -> T) := match m with
 | t => wtauto
 | l a => wauto (l a)
end.

Lemma wtaut_wtauto : forall O f f', wtaut O f f' -> wtauto f f'.
intros m f f' h. eapply weaker_refl_trans_fun. apply aut_aut. apply h.
Qed.

Lemma waut_wauto : forall O m f f', waut O m f f' -> wauto m f f'.
intros O m f f' h.
destruct h as [g h]. destruct h as [g' h]. destruct h as [h1 h]. destruct h as [h h2].
exists g. exists g'.
split; try split; try apply (wtaut_wtauto O); try assumption.
apply aut_aut with O. assumption.
Qed.

Lemma whaut_whauto : forall O m f f', whaut O m f f' -> whauto m f f'.
intros O m f f'.
induction m; simpl; intros h.
apply wtaut_wtauto with O; assumption.
apply waut_wauto with O; assumption.
Qed.


End op_trans.



Arguments wtaut [_] _ _ _.
Arguments waut [_] _ _ _ _.
Arguments whaut [_] _ _ _ _.

(* correspondance between the base (weak) LTS and the LTS over operators *)
Section aut_bsim.
Variable T:LTS.
Variable O : Op T.

Lemma whaut_whtrans : forall (f f' : T-> T) m, (whaut O m f f' -> forall x, whtrans m (f x) (f' x)).
intros f f' m.
induction m; simpl.
+ intros h x. induction h as [f g|f |f g h].
  - unfold wttrans. apply rt_step. destruct H as [o1 H]. destruct H as [o2 H]. apply (H x).
  - rewrite (H x). apply rt_refl.
  - eapply rt_trans; eassumption.
+ intros h x. destruct h. destruct H. destruct H. destruct H0. exists (x0 x).
  split. apply rel_fall_fun. apply (wtaut_wtauto) with O. assumption.
  exists (x1 x). split. apply H0.
  apply rel_fall_fun. apply wtaut_wtauto with O. apply H1.
Qed.



End aut_bsim.

(* Composition and autonomous transitions *)
Section aut_comp.
Variable T : LTS.
Variable O : Op T.

Lemma aut_comp : forall f g h m, op O h -> aut O m f g -> aut O m (comp f h) (comp g h).
intros f g h m hop autfg. destruct autfg as [fop autfg]. destruct autfg as [gop autfg].
split; try split; [ apply (clos_comp T O)|apply (clos_comp T O) | ]; try assumption.
unfold comp; simpl. intros x. apply autfg.
Qed.


Lemma wtaut_comp : forall f g h, op O h -> wtaut O f g -> wtaut O (comp f h) (comp g h).
intros f g h oph autfg. induction autfg as [f g autfg | f | f f' g ].
+ apply rtf_step. apply aut_comp; assumption.
+ apply rtf_refl. apply ext_eq_comp; try assumption. ext.
+ apply rtf_trans with (comp f' h). apply IHautfg1. apply IHautfg2.
Qed.

Lemma waut_comp : forall f g h m, op O h -> waut O m f g -> waut O m (comp f h) (comp g h).
intros f g h m hop autfg.
destruct autfg as [f' autfg]. destruct autfg as [g' autfg].
exists (comp f' h). exists (comp g' h). split; try split.
apply wtaut_comp; [apply hop | apply autfg].
apply aut_comp; [apply hop | apply autfg].
apply wtaut_comp;  [apply hop | apply autfg].
Qed.


End aut_comp.


(* Autonomous transitions and extensional equality *)
Section aut_extensional.
Variable T:LTS.
Variable O : Op T.

Lemma aut_ext : forall f g f' g', ext_eq f f' -> ext_eq g g' -> forall m, (aut O m f g -> aut O m f' g').
intros f g f' g' e1 e2 m h.
destruct h as [o h]. destruct h as [o' h]. split; [|split]. (eapply (clos_ext T O)). apply o. apply e1.
(eapply (clos_ext T O)). apply o'. apply e2.
intros x. destruct (e1 x); simpl. destruct (e2 x); simpl. apply h.
Qed.


Lemma wtaut_ext : forall f g f' g', ext_eq f f' -> ext_eq g g' -> wtaut O f g -> wtaut O f' g'.
intros f g f' g' e1 e2 h. revert e1 e2. revert f' g'. induction h; intros f' g' e1 e2.
* constructor.
  eapply aut_ext; eassumption.
* apply rtf_refl. ext.
* eapply rtf_trans. apply IHh1. assumption. apply ext_refl. apply IHh2. ext. ext.
Qed.


Lemma waut_ext : forall f g f' g' m, ext_eq f f' -> ext_eq g g' -> waut O m f g -> waut O m f' g'.
intros f g f' g' m e1 e2 tr. destruct tr as  [ h tr]. destruct tr as [h' tr]. destruct tr as [ tt tr]; destruct tr as [ vt tt'].
* exists h. exists h'. split; [|split]; [|assumption|]; eapply wtaut_ext; try eassumption; ext.
Qed.

Lemma whaut_ext : forall f g f' g' m, ext_eq f f' -> ext_eq g g' -> whaut O m f g -> whaut O m f' g'.
intros f g f' g' m. induction m.
* simpl. apply wtaut_ext.
* simpl. apply waut_ext.
Qed.



End aut_extensional.
