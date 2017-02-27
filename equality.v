
Lemma n1:
    forall D:Set,
    forall p:(D->D->Prop),
    ((forall x:D, (forall y:D, p x y)) -> (forall y:D, (forall x:D, p x y))).
  intros.
  specialize (H x y).
  exact H.
Qed.

Lemma n2:
    forall D:Set,
    forall p:(D->D->Prop),
    ((exists x:D, (exists y:D, p x y)) -> (exists y:D, (exists x:D, p x y))).
  intros.
  destruct H.
  destruct H.
  exists x0.
  exists x.
  exact H.
Qed.
