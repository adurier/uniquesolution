Require Import Relations.
Load divergences.


(* This file is dedicated to the definition of an opertor that 'protects its solutions' and the proof that if f 
    protects its solutions, it has a unique solution*)

Section sol_props.
Variable T : LTS.

(* Definition of 'having a unique solution for ~~' *)
Definition unique_sol : (T -> T) -> Prop := fun (f : T->T) => forall (x y : T), x ~~ (f x) -> y ~~ (f y) -> x ~~ y.

(* if x = f x, then x = f^n x *)
Lemma unfold_sol : forall (f : T -> T) (x : T) (n : nat), x ~~ (f x)  -> congruence f -> x ~~ (unfolding f n x).
intros f x n h h'.
induction n; simpl.
+ apply refl_bsim.
+ unfold comp. eapply bsim_trans. apply h. apply h'. apply IHn.
Qed.

End sol_props.


Arguments unique_sol [_] _.


Section protects.
Variable T : LTS.
Variable O : Op T.
Variable f : T -> T.
Hypothesis fop : op O f.
(* Definition of protects its solutions: every transition g x -m-> y where g is a reduct of f can be emulated by a finite
   unfolding of f, f^n -m-> f' such that f' x ~~ y *)
Definition protects : Prop := forall g x, op O g -> x ~~ (f x) -> comp_red O f g ->
  forall m y, whtrans m (g x) y -> exists g' n, op O g' /\ comp_red O f g' /\ whaut O m (comp g (unfolding f n)) g' /\ g' x ~~ y.

End protects.

Arguments protects [_] _ _ .

Section protects_unique.
Variable T : LTS.
Variable O : Op T.
Variable f : T -> T.
Hypothesis fop : op O f.
Hypothesis prot : protects O f.
Variable x y:T.
Hypothesis xsol : x ~~ (f x).
Hypothesis ysol : y ~~ (f y).

(* The bisimulation candidate to prove that if f protects its solutions and x and y are two of its solutions,
    then x ~~ y *)
Definition rel_prot : relation T := fun p q => exists c, op O c /\ comp_red O f c /\ p ~~ (c x) /\ q ~~ (c y).


(* The proof that the bisimulation candidate is a bisimulation *)
Lemma bsim_rel_prot : bsim_rel rel_prot.
split.
+ intros p q p' R tr.
  destruct R as [c s]; destruct s as [opc s]; destruct s as [red s]; destruct s as [b b'].
  destruct (bsim_diag T p (c x) b m p' tr) as [q'' s]; destruct s as [wt b''].
  edestruct (prot c x opc xsol red m  q'' wt) as [c' s]; destruct s as [n s].
  destruct s as [opc' s]; destruct s as [redc' s]; destruct s as [awt bc'].
  assert (h := whaut_whtrans T O (comp c (unfolding f n)) c' m awt y).
  destruct (bsim_diag_weak T (comp c (unfolding f n) y) q (c' y) m) as [q']; [ |apply h | ].
  - eapply bsim_trans; [|eapply sym_bsim; eassumption]. unfold comp. apply (cong T O c opc).
    apply sym_bsim. apply unfold_sol. apply ysol. apply (cong T O f fop).
  - exists q'. split; [apply H|].
    exists c'; split; auto; split; auto; split; auto.
    eapply bsim_trans. apply b''. apply sym_bsim. apply bc'.
    apply sym_bsim; auto. apply H.
+ intros q p q' R tr.
  destruct R as [c s]; destruct s as [opc s]; destruct s as [red s]; destruct s as [b b'].
  destruct (bsim_diag T q (c y) b' m q' tr) as [p'' s]; destruct s as [wt b''].
  edestruct (prot c y opc ysol red m  p'' wt) as [c' s]; destruct s as [n s].
  destruct s as [opc' s]; destruct s as [redc' s]; destruct s as [awt bc'].
  assert (h := whaut_whtrans T O (comp c (unfolding f n)) c' m awt x).
  destruct (bsim_diag_weak T (comp c (unfolding f n) x) p (c' x) m) as [p']; [ |apply h | ].
  - eapply bsim_trans; [|eapply sym_bsim; eassumption]. unfold comp. apply (cong T O c opc).
    apply sym_bsim. apply unfold_sol. apply xsol. apply (cong T O f fop).
  - exists p'. split; [apply H|].
    exists c'; split; auto; split; auto; split; auto.
    apply sym_bsim; auto. apply H.
    eapply bsim_trans. apply b''. apply sym_bsim. apply bc'.
Qed.

Lemma unique_aux : x ~~ y.
exists rel_prot.
split.
+ exists f. split. apply fop.
  split. constructor. auto. 
+ apply bsim_rel_prot.
Qed.

End protects_unique.

(* The final lemma *)
Lemma protects_unique : forall T (O : Op T) (f : T -> T), op O f -> protects O f -> unique_sol f.
intros T O f opf prot; intros x y xsol ysol.
apply unique_aux with O f; auto.
Qed.

