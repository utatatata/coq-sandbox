Inductive and (A B:Prop) : Prop :=
  conj : A -> B -> A /\ B
where "A /\ B" := (and A B) : type_scope.

Goal forall P Q, P /\ Q -> Q /\ P.
Proof.
  intros.
  elim H.
  intros.
  apply conj.
    - trivial.
    - trivial.
Qed.