Inductive nat : Set :=
  | Z : nat
  | S : nat -> nat.

Fixpoint add n m :=
  match n with
  | Z => m
  | S p => S (add p m)
  end.

Lemma eq1 : forall n, add n Z = add Z n.
Proof.
  intros.
  elim n.
  - trivial.
  - intros.
    simpl.
    rewrite H.
    simpl.
    trivial.
Qed.

Lemma eq2 : forall n m, add (S n) m = add n (S m).
Proof.
  intros.
  elim n.
  - simpl.
    trivial.
  - intros.
    simpl.
    f_equal.
    inversion H.
    rewrite H1.
    trivial.
Qed.

Goal forall n m, add n m = add m n.
Proof.
  intros.
  elim n.
  - rewrite eq1.
    trivial.
  - intros.
    simpl.
    rewrite H.
    rewrite <- eq2.
    simpl.
    trivial.
Qed.