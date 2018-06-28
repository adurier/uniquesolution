Load unique_solution_steps.

(* Statement of the unique solution theorem, with a well-foundedness hypothesis over the tau
    reduction relation (instead of a non-divergence hypothesis) *)
Section unique_solution_wf.
Variable T : LTS.
Variable O : Op T.
Variable f : T -> T.
Hypothesis fop : op O f.
Hypothesis gf :  guarded (op O) f.


(* This is the tau reduction relation: it relates g and h if there is a tau autonomous transition from the composition
    of g and f to h, and if both g and h can be obtained by autonomous transitions from f (this is the meaning of 
    comp_red). The definition of red_tau is in the last section of termination.v *)
Definition reduction_tau := red_tau O f (comp_red O f).

Hypothesis wf_reduction : well_founded reduction_tau.


(* Main Theorem *)
Theorem unique_solution : unique_sol f.

exact (protects_unique T O f fop (op_protects_wf T O f fop gf wf_reduction)).
Qed.

End unique_solution_wf.



(* Statement of the unique solution theorem, using the excluded middle axiom, with a non-divergence hypothesis. *)
Section unique_solution_ExcludedMiddle.

Hypothesis ExcludedMiddle : forall A, A \/ ~A.

Theorem unique_solution_EM : forall (T : LTS) (O : Op T) (f : T -> T),
  op O f ->
  guarded (op O) f -> 
  ~ op_div O f
-> unique_sol f.

exact (fun T O f fop gf ndiv => protects_unique T O f fop (op_protects_EM T O f fop gf ExcludedMiddle ndiv)).
Qed.


End unique_solution_ExcludedMiddle.