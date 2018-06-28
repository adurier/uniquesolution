Require Import Relations.
Require Import Wf.
Load unique_sol_prop.

(* Mostly technical lemmas regarding divergences, excluded middle, well-foundedness, and termination *)
Definition EM := forall A : Prop, A \/ ~ A.

(* A and S define a base set (it will be, for us, the set of reducts of the operator which defines the equation
    we're interested into), R is the relation we assume terminates or does not 'diverge', and P is 
    the property we want to prove and that holds if we find a maximal element. *)
Section termination.
Variable A : Type.
Variable S : A -> Prop.
Variable R : relation A.
Variable P : Prop.

CoInductive divR : A -> Prop :=
 | stepR : forall x y, R x y -> divR y -> S x -> divR x.

CoInductive divP : A -> Prop :=
 | stepR' : forall x y, R x y -> divP y -> S x -> divP x
 | stopP : forall x, P -> S x -> divP x.


Lemma divP_S : forall x, divP x -> S x.
intros x dp. inversion dp; assumption.
Qed.


Section termination_EM.
Hypothesis EM : forall A : Prop, A \/ ~ A.

Lemma double_neg : forall (B : Prop), ~ ~ B -> B.
intros B f. destruct (EM B) as [|h]; [assumption|]. exfalso; apply f; apply h.
Qed.


Lemma div_or : forall x, divP x -> (~ P) -> divR x.
intros x h f. revert h. revert x.
cofix. intros n h.
destruct h.
apply stepR with y; try assumption. apply div_or; assumption.
exfalso. apply f. assumption. 
Qed.


Lemma notdiv_P : forall x, divP x -> (~ divR x) -> P.
intros x d nd.
apply double_neg. intro f. assert (h := div_or x d). apply (nd). apply h.
apply f.
Qed.

End termination_EM.


Section Wf.
Definition subrevR : relation A := fun x y => R y x /\ S x /\ S y.
Hypothesis wf : well_founded subrevR.

Check well_founded_ind.

Lemma notdiv_P_Wf : forall x, divP x -> P.
apply (well_founded_ind wf (fun x => divP x -> P)).
intros x rec dpx. destruct dpx as [x y r dpy sx | x p sx].
* apply (rec y). split; try split; try apply (divP_S y); assumption. assumption.
* apply p.
Qed. 


End Wf.

End termination.




Section div_termination.
Variable T : LTS.
Variable O : Op T.
Variable c : T -> T.
Hypothesis opc : op O c.
Variable S : (T -> T) -> Prop.

Definition rel_div : (T -> T) -> (T -> T) -> Prop := fun  f g =>
 aut O t (comp f c) g.

Lemma divR_div : forall (f : T -> T), (divR (T -> T) S rel_div f) -> (comp_top_div O c f).
cofix. intros f dR.
destruct dR as [x y rd dR sx]. apply cdstep with y. exact rd.
apply divR_div. apply dR.
Qed.


Lemma notdiv_div_P : EM -> forall f (P : Prop), divP (T -> T) S rel_div P f -> (~ comp_top_div O c f)
-> P.
intros EM f P dP nd.
apply notdiv_P with (T -> T) S rel_div f; [apply EM| apply dP |].
intros dR. apply nd. apply divR_div. apply dR.
Qed.


Definition red_tau := subrevR (T -> T) S rel_div.

Lemma wf_P : forall f (P : Prop), well_founded red_tau -> divP (T -> T) S rel_div P f 
-> P.
intros f P wf dP.
apply notdiv_P_Wf with (T -> T) S rel_div f. apply wf. apply dP.
Qed.


End div_termination.


Arguments red_tau [_].


(* Small lemma to prove that a relation that is well-founded is still well-founded over a smaller set *)
Lemma wf_wf : forall T (O : Op T) c (S S' : (T -> T) -> Prop), op O c -> (forall x, S' x -> S x) -> well_founded (red_tau O c S) -> well_founded (red_tau O c S').
intros T O c S S' opc wk wf x.
apply (well_founded_ind wf (fun x => Acc (red_tau O c S') x)).
intros x' rec. constructor. intros y rt. apply (rec y). unfold red_tau. unfold subrevR. split; try split; try apply rt.
apply wk. apply rt.
apply wk. apply rt.
Qed.





















