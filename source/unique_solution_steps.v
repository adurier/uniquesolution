Load termination.

(* Main elements of the proof: we start with an autonomous operator f, a solution x of x = f(x), 
    and a weak transition from g(x) (where g is a reduct of f), let's say g(x) =a=> y.
    Then we build a sequence of operators, and either it does not stop and we build
    a divergence, either it does and we can emulate this transition with a finite unfolding of f, i.e.
    g(f^n(x)) =a=> f'(x) ~~ y *)

(* This first section treats in the case of a visible weak transition: =a=>. If the construction stops
    in this section, then we built a transition g(f^n(x)) =a=> gn(x)  but we don't always have that gn(x) ~~ y;
    however gn(x) => yn ~~ y , and we treat this transition in the section seq_visible2 *)
Section seq_visible.
Variable T : LTS.
Variable O : Op T.
Variable f : T -> T.
Variable x : T.
(* f is the equation, x its solution *)
Hypothesis x_sol : f x ~~ x.
(* g is the context from which there is a transition; it needs to be a reduct of f *)
Variable g : T -> T.
Hypothesis redfg : comp_red O f g.
Variable y : T.
Variable a : label (l:=T).
(* This is the transition we consider and emulate *)
Hypothesis itr : wtrans (l a) (g x) y.
(* f and g are operators, f is guarded or autonomous *)
Hypothesis fop : op O f.
Hypothesis gop : op O g.
Hypothesis gf : guarded (op O) f.


Section step_visible1.
(* This is the predicate verified by any context/operator of the sequence that we built; 
    if gn verifies seq_op, then we have g(f^n(x)) => gn(x) =a=> yn ~~ y *)
Definition seq_op (gn : T -> T) := (exists yn, yn ~~ y /\ wtrans (l a) (gn x) yn) /\ (exists n, wtaut O (comp g (unfolding f n)) gn) /\ 
op O gn /\ comp_red O f gn.

(* This is the predicate verified by gn when we stop: it means the visible transition is now an autonomous
    transition (g(f^n(x)) =a=> (gn(x)) *)
Definition seq_vis1 (gn : T -> T) := (exists yn, yn ~~ y /\ wttrans (gn x) yn) /\ (exists n, waut O (l a) (comp g (unfolding f n)) gn) 
/\ op O gn /\ comp_red O f gn.



(* One step in the construction of the first sequence: we start from gn, we build gn+1 and show that either
    it verifies seq_op and we can continue, or it verifies seq_vis1 and we stop. *)
Variable gn : T -> T.
Hypothesis seqop : seq_op gn.

(* Some properties of gn *)
Lemma step_bsim : (comp gn f) x ~~ (gn x).
unfold comp.
apply (cong T O gn).
apply seqop.
apply x_sol.
Qed.


Lemma step_diag : exists yn', whtrans (l a) ((comp gn f) x) yn' /\ y ~~ yn'.
destruct seqop as [h so']; destruct h as [yn hn].
destruct (bsim_diag_weak T (gn x) (comp gn f x) yn (l a)) as [yn' h].
apply sym_bsim. apply step_bsim. simpl. apply hn.
exists yn'. split; [apply h|]. apply bsim_trans with yn.
apply sym_bsim. apply hn. apply h.
Qed.

Lemma gg : guarded (op O) (comp gn f).
apply (leftguard T O gn f).
apply seqop.
apply gf.
Qed. 

(* Technical lemma to be able to use associativity of composition 
    and commutation of composition of f and its unfoldings *)
Lemma ext_comp : forall n, ext_eq (comp g (comp f (unfolding f n))) (comp (comp g (unfolding f n)) f).
intros n. intros s. 
assert (eeq : ext_eq ((comp f (unfolding f n))) (comp ((unfolding f n)) f)).
intros s'. simpl. rewrite (unfold_right T f n s'). trivial. specialize (eeq s).
unfold comp. unfold comp in eeq. rewrite eeq. reflexivity.
Qed.

(* We prove that gn+1 exists *)
Lemma proof_step_vis1 : (exists gn', seq_op gn' /\ aut O t (comp gn f) gn') \/ (exists gn', seq_vis1 gn' 
/\ aut O (l a) (comp gn f) gn').
destruct step_diag as [yn' h]. destruct h as [tr eqn'].
simpl in tr. destruct tr as [z h]. destruct h as [wtr1 h]. destruct h as [z' h].
destruct h as [vtr wtr2]. remember (comp gn f x) as gnfx.
destruct (clos_refl_trans_one_or T (trans t) gnfx z wtr1) as [ | ex]; [subst|].
+ right. destruct gg as [d gd]; clear d. destruct (gd x z' (l a) vtr) as [gn' hn'].
  exists gn'. repeat (try split); try apply hn'.
  - exists yn'. split. apply sym_bsim. apply eqn'. 
    destruct hn' as [opgn' h'']. destruct h'' as [s autr].
    subst. apply wtr2.
  - destruct seqop as [_ seqop']. destruct seqop' as [exn _]. destruct exn as [n hn].
    exists (S n). exists (comp gn f). exists gn'. repeat try split;
     [| apply (clos_comp T O); [apply seqop|apply fop] | apply hn' | apply hn'|apply rtf_refl].
    simpl. eapply wtaut_ext. apply ext_sym. apply ext_comp.
     ext. apply wtaut_comp. apply fop. apply hn. ext.
  - apply comp_red_right with gn (l a). destruct seqop as [_ hh]; destruct hh as [_ hh]; destruct hh as [_ cr]; exact cr.
    split; [|split; apply hn']. apply (clos_comp T O); [apply seqop|assumption].
  - apply (clos_comp T O); [apply seqop|assumption].
+ destruct ex as [zz h].
  left. destruct gg as [d gd]; clear d. subst.
  destruct h as [h wtr3].
  destruct (gd x zz t h) as [gn' h0]. exists gn'. repeat (try split); try apply h0.
  destruct h0 as [opgn' h0]; destruct h0 as [eqzz h0]. subst.
  - exists yn'. split; [apply sym_bsim; assumption|]. 
    exists z. split. assumption. exists z'. split; assumption.
  - destruct seqop as [_ seqop']. destruct seqop' as [exn _]. destruct exn as [n hn].
    exists (S n). simpl.  eapply wtaut_ext. apply ext_sym. apply ext_comp.
     ext. eapply rtf_trans. apply wtaut_comp. apply fop. apply hn.
    apply rtf_step. split; try split; [| |apply h0]. apply (clos_comp T O). apply seqop. apply fop.
    apply h0.
  - eapply comp_red_right with gn t. destruct seqop as [_ hh]; destruct hh as [_ hh]; destruct hh as [_ cr]; exact cr.
    split; [|split; apply h0]. apply (clos_comp T O); [apply seqop|assumption].
  - apply (clos_comp T O); [apply seqop|assumption].
Qed.


End step_visible1.



(* We use the proof for one step above to prove that we can stop. We start from g as g0, and then 
    use either non divergence and excluded middle, or well-foundedness, to show that the construction stops *)
Section proof_vis1.


Lemma seqopg : seq_op g.
repeat try split.
+ exists y. split; [apply refl_bsim|apply itr].
+ exists 0. simpl. apply rtf_refl. ext.
+ apply gop.
+ apply redfg.
Qed.

Lemma divP_vis1 : forall gn, seq_op gn -> divP (T -> T) seq_op (rel_div T O f) (exists gn', seq_vis1 gn') gn.
cofix. intros gn seqop. destruct proof_step_vis1 with gn as [exn'|exn']; [apply seqop| |];
destruct exn' as [gn' hn'].
+ apply stepR' with gn'; [| apply divP_vis1| assumption]; apply hn'. 
+ apply stopP. exists gn'. apply hn'. apply seqop.
Qed.

(* With excluded middle and non divergence *)
Section vis1_EM.
Hypothesis EM : forall A, A \/ ~A.


Lemma opdiv_div : ~ op_div O f -> forall gn, comp_red O f gn -> ~ comp_top_div O f gn.
intros div gn cr topdiv. apply div. apply red_div. exists gn; split; assumption.
Qed.


Lemma vis1_EM : ~ op_div O f -> exists gn, seq_vis1 gn.
intros ndiv.
destruct (notdiv_div_P T O f seq_op EM g (exists gn', seq_vis1 gn')) as [gn h]. apply divP_vis1. apply seqopg.
apply opdiv_div; assumption.
exists gn. apply h.
Qed.

End vis1_EM.
(* With well-foundedness of the reverse of the tau reduction relation over the reducts of f *)
Section vis1_Wf.
Hypothesis wf: well_founded (red_tau O f (comp_red O f)).

Lemma wf_seq_op : well_founded (red_tau O f seq_op).
eapply wf_wf; [assumption| | apply wf ]. intros. apply H.
Qed.

Lemma vis1_Wf: exists gn, seq_vis1 gn.
destruct (wf_P T O f seq_op g (exists gn', seq_vis1 gn') wf_seq_op) as [gn h]. apply divP_vis1. apply seqopg.
exists gn. apply h.
Qed.


End vis1_Wf.

End proof_vis1.


(* Same as step_visible, except the visible transition is already done by the gn's, and we want to complete it so that
    gn(x) ~~ y *)
Section step_visible2.
(* Verified by the gn's we build: we have g(f^n(x)) =a=> gn(x) => yn ~~ y *)
Definition seq_vis2 gn := (exists yn, yn ~~ y /\ wttrans (gn x) yn) /\ (exists n, waut O (l a) (comp g (unfolding f n)) gn) /\ 
op O gn /\ comp_red O f gn.

(* Verified by the gn when we stop: g(f^n(x)) =a=> gn(x) ~~ y *)
Definition seq_end gn := (comp gn f x ~~ y) /\ (exists n, waut O (l a) (comp g (unfolding f n)) gn) /\ 
op O gn /\ comp_red O f gn.

(* One step: we start from gn... Proof is almost the same as previously. *)
Variable gn : T -> T.
Hypothesis seqop : seq_vis2 gn.


Lemma step_bsim2 : (comp gn f) x ~~ (gn x).
unfold comp.
apply (cong T O gn).
apply seqop.
apply x_sol.
Qed.


Lemma step_diag2 : exists yn', wttrans ((comp gn f) x) yn' /\ y ~~ yn'.
destruct seqop as [h so']; destruct h as [yn hn].
destruct (bsim_diag_weak T (gn x) (comp gn f x) yn t) as [yn' h].
apply sym_bsim. apply step_bsim2. simpl. apply hn.
exists yn'. split; [apply h|]. apply bsim_trans with yn.
apply sym_bsim. apply hn. apply h.
Qed.

Lemma gg2 : guarded (op O) (comp gn f).
apply (leftguard T O gn f).
apply seqop.
apply gf.
Qed.


Lemma waut_cons_tau : forall f g h m, waut O m f g -> wtaut O g h -> waut O m f h.
intros i j k m wt tt. destruct wt as [i' wt]; destruct wt as [j' wt]; destruct wt as [tt' wt]; destruct wt as [tr tt''].
exists i'. exists j'. split; try assumption. split; try assumption. eapply rtf_trans; eassumption.
Qed.

Lemma proof_step_vis2 : (exists gn', seq_vis2 gn' /\ aut O t (comp gn f) gn') \/ (seq_end gn).
destruct step_diag2 as [yn' h]. destruct h as [tr eqn'].
simpl in tr. remember (comp gn f x) as gnfx.
destruct (clos_refl_trans_one_or T (trans t) gnfx yn' tr) as [ | ex]; [subst|].
+ right. repeat try split.
  - apply sym_bsim. apply eqn'.
  - destruct seqop as [_ seqop']. destruct seqop' as [exn _]. destruct exn as [n hn].
    exists n. simpl. apply hn.
  - apply seqop.
  - apply seqop.
+ destruct ex as [zz h].
  left. destruct gg2 as [d gd]; clear d. subst.
  destruct h as [h wtr3].
  destruct (gd x zz t h) as [gn' h0]. exists gn'. repeat (try split); try apply h0.
  destruct h0 as [opgn' h0]; destruct h0 as [eqzz h0]. subst.
  - exists yn'. split; [apply sym_bsim; assumption|]. apply wtr3.
  - destruct seqop as [_ seqop']. destruct seqop' as [exn _]. destruct exn as [n hn].
    exists (S n). simpl. eapply waut_ext. apply ext_sym. apply ext_comp.
     ext. apply waut_cons_tau with (comp gn f).
    apply waut_comp. apply fop. apply hn. apply rtf_step. split; [|split; apply h0].
    apply (clos_comp T O). apply seqop. apply fop.
  - eapply comp_red_right with gn t. destruct seqop as [_ hh]; destruct hh as [_ hh]; destruct hh as [_ cr]; exact cr.
    split; [|split; apply h0]. apply (clos_comp T O); [apply seqop|assumption].
  - apply (clos_comp T O); [apply seqop|assumption].
Qed.


End step_visible2.


(* We now end the proof (in the visible case), as previously, with either non divergence or well-foundedness*)
Section proof_vis2.

Lemma divP_vis2 : forall gn, seq_vis2 gn -> divP (T -> T) seq_vis2 (rel_div T O f) (exists gn', seq_end gn') gn.
cofix. intros gn seqop. destruct proof_step_vis2 with gn as [exn'|exn']; [apply seqop| |].
+ destruct exn' as [gn' hn']. apply stepR' with gn'; [| apply divP_vis2| assumption]; apply hn'. 
+ apply stopP. exists gn. apply exn'. apply seqop.
Qed.

Section vis2_EM.
Hypothesis EM : forall A, A \/ ~A.


Lemma seqvis2 : ~ op_div O f -> exists g', seq_vis2 g'.
intros F. destruct (vis1_EM EM F) as [g' h].
destruct h as [exn h]. destruct h as [exnn h].
exists g'; repeat try split.
+ destruct exn as [yn h']. exists yn. apply h'.
+ destruct exnn as [n hn]. exists n. apply hn.
+ apply h.
+ apply h.
Qed.

Lemma vis_EM : ~ op_div O f -> exists gn, seq_end gn.
intros ndiv. destruct (seqvis2 ndiv) as [g' seqop'].
destruct (notdiv_div_P T O f seq_vis2 EM g' (exists gn, seq_end gn)) as [gn h]. apply divP_vis2. apply seqop'.
apply opdiv_div. apply ndiv. apply seqop'.
exists gn. apply h.
Qed.

End vis2_EM.

Section vis2_Wf.
Hypothesis wf: well_founded (red_tau O f (comp_red O f)).

Lemma wf_seq_vis2 : well_founded (red_tau O f seq_vis2).
eapply wf_wf; [assumption| | apply wf ]. intros. apply H.
Qed.

Lemma seqvis2_wf : exists g', seq_vis2 g'.
destruct (vis1_Wf wf) as [g' h]. 
destruct h as [exn h]. destruct h as [exnn h].
exists g'; repeat try split.
+ destruct exn as [yn h']. exists yn. apply h'.
+ destruct exnn as [n hn]. exists n. apply hn.
+ apply h.
+ apply h.
Qed.

Lemma vis_Wf: exists gn, seq_end gn.
destruct (seqvis2_wf) as [g' seqop].
destruct (wf_P T O f seq_vis2 g' (exists gn, seq_end gn) wf_seq_vis2) as [gn h]. apply divP_vis2. assumption.
exists gn. apply h.
Qed.


End vis2_Wf.

 
End proof_vis2.


End seq_visible.








(* Same as the two previous sections, but for a tau transition: we start from g(x) => y. 
    Then there is only one sequence to build instead of two: we don't have to first produce a
    visible transition*)
Section seq_tau.
Variable T : LTS.
Variable O : Op T.
Variable f : T -> T.
Variable x : T.
Hypothesis x_sol : f x ~~ x.
Variable g : T -> T.
Hypothesis redfg : comp_red O f g.
Variable y : T.
Hypothesis itr : wttrans (g x) y.
Hypothesis fop : op O f.
Hypothesis gop : op O g.
Hypothesis gf : guarded (op O) f.



Definition seq_tau (gn : T -> T) := (exists yn, yn ~~ y /\ wttrans (gn x) yn) /\ (exists n, wtaut O (comp g (unfolding f n)) gn) /\ 
op O gn /\ comp_red O f gn.

Definition seq_end' gn := (comp gn f x ~~ y) /\ (exists n, wtaut O (comp g (unfolding f n)) gn) /\ 
op O gn /\ comp_red O f gn.


Section step_tau.
Variable gn : T -> T.
Hypothesis seqtau : seq_tau gn.

Lemma step_bsim_tau : (comp gn f) x ~~ (gn x).
unfold comp.
apply (cong T O gn).
apply seqtau.
apply x_sol.
Qed.


Lemma step_diagt : exists yn', wttrans ((comp gn f) x) yn' /\ y ~~ yn'.
destruct seqtau as [h so']; destruct h as [yn hn].
destruct (bsim_diag_weak T (gn x) (comp gn f x) yn t) as [yn' h].
apply sym_bsim.  apply step_bsim_tau. simpl. apply hn.
exists yn'. split; [apply h|]. apply bsim_trans with yn.
apply sym_bsim. apply hn. apply h.
Qed.

Lemma ggt : guarded (op O) (comp gn f).
apply (leftguard T O gn f).
apply seqtau.
apply gf.
Qed.


Lemma proof_step_tau : (exists gn', seq_tau gn' /\ aut O t (comp gn f) gn') \/ (seq_end' gn).
destruct step_diagt as [yn' h]. destruct h as [tr eqn'].
simpl in tr. remember (comp gn f x) as gnfx.
destruct (clos_refl_trans_one_or T (trans t) gnfx yn' tr) as [ | ex]; [subst|].
+ right. repeat try split.
  - apply sym_bsim. apply eqn'.
  - destruct seqtau as [_ seqtau']. destruct seqtau' as [exn _]. destruct exn as [n hn].
    exists n. simpl. apply hn.
  - apply seqtau.
  - apply seqtau.
+ destruct ex as [zz h].
  left. destruct ggt as [d gd]; clear d. subst.
  destruct h as [h wtr3].
  destruct (gd x zz t h) as [gn' h0]. exists gn'. repeat (try split); try apply h0.
  destruct h0 as [opgn' h0]; destruct h0 as [eqzz h0]. subst.
  - exists yn'. split; [apply sym_bsim; assumption|]. apply wtr3.
  - destruct seqtau as [_ seqop']. destruct seqop' as [exn _]. destruct exn as [n hn].
    exists (S n). simpl. eapply wtaut_ext. apply ext_sym. apply ext_comp.
     ext. eapply rtf_trans.
    apply wtaut_comp. apply fop. apply hn. apply rtf_step. split; [|split; apply h0].
    apply (clos_comp T O). apply seqtau. apply fop.
  - eapply comp_red_right with gn t. destruct seqtau as [_ hh]; destruct hh as [_ hh]; destruct hh as [_ cr]; exact cr.
    split; [|split; apply h0]. apply (clos_comp T O); [apply seqtau|assumption].
  - apply (clos_comp T O); [apply seqtau|assumption].
Qed.

End step_tau.

Lemma divP_tau : forall gn, seq_tau gn -> divP (T -> T) seq_tau (rel_div T O f) (exists gn', seq_end' gn') gn.
cofix. intros gn seqop. destruct proof_step_tau with gn as [exn'|exn']; [apply seqop| |].
+ destruct exn' as [gn' hn']. apply stepR' with gn'; [| apply divP_tau| assumption]; apply hn'. 
+ apply stopP. exists gn. apply exn'. apply seqop.
Qed.


Lemma seqtaug : seq_tau g.
repeat try split.
+ exists y. split; [apply refl_bsim|apply itr].
+ exists 0. simpl. apply rtf_refl. ext.
+ apply gop.
+ apply redfg.
Qed.

Section tau_EM.
Hypothesis EM : forall A, A \/ ~A.

Lemma tau_EM : ~ op_div O f -> exists gn, seq_end' gn.
intros ndiv. destruct (seqtaug) as [g' seqop'].
destruct (notdiv_div_P T O f seq_tau EM g (exists gn, seq_end' gn)) as [gn h]. apply divP_tau. apply seqtaug.
apply opdiv_div. apply ndiv. apply seqop'.
exists gn. apply h.
Qed.

End tau_EM.

Section tau_Wf.
Hypothesis wf: well_founded (red_tau O f (comp_red O f)).

Lemma wf_tau : well_founded (red_tau O f seq_tau).
eapply wf_wf; [assumption| | apply wf ]. intros. apply H.
Qed.


Lemma tau_Wf: exists gn, seq_end' gn.
destruct (seqtaug) as [g' seqop'].
destruct (wf_P T O f seq_tau g (exists gn, seq_end' gn) wf_tau) as [gn h]. apply divP_tau. apply seqtaug.
exists gn. apply h.
Qed.

End tau_Wf.


End seq_tau.




(* We can now prove that if f is autonomous and non divergent (or that the tau reduction relation over
    the set of reducts of f is well-founded) then f protects its solutions. *)
Section aut_op_protects.
Variable T : LTS.
Variable O : Op T.
Variable f : T -> T.
Hypothesis fop : op O f.
Hypothesis gf : guarded (op O) f.


Section protects_EM.
Hypothesis EM : forall A, A \/ ~A.
Hypothesis ndiv : ~ op_div O f.

Lemma op_protects_EM : protects O f.
unfold protects. intros g x gop x_sol redfg m y itr.
induction m as [|a].
+ apply sym_bsim in x_sol.
  simpl in *. destruct (tau_EM T O f x x_sol g redfg y itr fop gop gf EM ndiv) as [gn hn].
  exists gn. destruct hn as [eqn hn]. destruct hn as [exn h]. destruct exn as [n hn].
  exists n. repeat try split; try apply h; try assumption.
  apply bsim_trans with (comp gn f x); [|apply eqn]. unfold comp; simpl. apply (cong T O ).
  apply h. apply sym_bsim. apply x_sol.
+ apply sym_bsim in x_sol.
  simpl in *. destruct (vis_EM T O f x x_sol g redfg y a itr fop gop gf EM ndiv) as [gn hn].
  exists gn. destruct hn as [eqn hn]. destruct hn as [exn h]. destruct exn as [n hn].
  exists n. repeat try split; try apply h; try assumption.
  apply bsim_trans with (comp gn f x); [|apply eqn]. unfold comp; simpl. apply (cong T O ).
  apply h. apply sym_bsim. apply x_sol.
Qed.

End protects_EM.

Section protects_Wf.
Hypothesis wf: well_founded (red_tau O f (comp_red O f)).

Lemma op_protects_wf : protects O f.
unfold protects. intros g x gop x_sol redfg m y itr.
induction m as [|a].
+ apply sym_bsim in x_sol.
  simpl in *. destruct (tau_Wf T O f x x_sol g redfg y itr fop gop gf wf) as [gn hn].
  exists gn. destruct hn as [eqn hn]. destruct hn as [exn h]. destruct exn as [n hn].
  exists n. repeat try split; try apply h; try assumption.
  apply bsim_trans with (comp gn f x); [|apply eqn]. unfold comp; simpl. apply (cong T O ).
  apply h. apply sym_bsim. apply x_sol.
+ apply sym_bsim in x_sol.
  simpl in *. destruct (vis_Wf T O f x x_sol g redfg y a itr fop gop gf wf) as [gn hn].
  exists gn. destruct hn as [eqn hn]. destruct hn as [exn h]. destruct exn as [n hn].
  exists n. repeat try split; try apply h; try assumption.
  apply bsim_trans with (comp gn f x); [|apply eqn]. unfold comp; simpl. apply (cong T O ).
  apply h. apply sym_bsim. apply x_sol.
Qed.



End protects_Wf.




End aut_op_protects.



