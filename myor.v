Inductive or (A B:Prop) : Prop :=
  | or_introl : A -> A \/ B
  | or_intror : B -> A \/ B
where "A \/ B" := (or A B) : type_scope.


Goal forall P Q, P \/ Q -> Q \/ P.
Proof.
  intros.
  elim H.
  - intros.
    apply or_intror.
    trivial.
  - intros.
    apply or_introl.
    trivial.
Qed.

(* Lemma myor_ind is automatically defined. *)
(* "elim" uses it. *)