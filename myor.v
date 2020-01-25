Inductive myor (A B:Prop) : Prop :=
  | myor_introl : A -> A \/ B
  | myor_intror : B -> A \/ B
where "A \/ B" := (myor A B) : type_scope.


Goal forall A B, (myor A B) -> (myor B A).
Proof.
  intros.
  elim H.
  - intros.
    apply myor_intror.
    trivial.
  - intros.
    apply myor_introl.
    trivial.
Qed.

(* Lemma myor_ind is automatically defined. *)
(* "elim" uses it. *)