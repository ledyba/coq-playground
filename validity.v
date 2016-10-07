
Lemma it_is_valid_if_D_is_not_empty:
  ~(forall (D : Set) (p : D -> Prop),
     ((forall x : D, p(x)) -> (exists x : D, p(x)))).
  intros contra.
  Variable p : Empty_set -> Prop.
  specialize (contra Empty_set p).
  destruct contra.
  apply Empty_set_ind.
  contradiction x.
Qed.

Lemma p1:
  forall (D:Set) (a:D->Prop) (b:D->Prop),
  (exists (x:D), a x /\ b x) ->  (exists (x:D), a x) /\   (exists (x:D), b x).
  intros.
  destruct H.
  destruct H as [A B].
  apply conj.
  exists x.
  exact A.
  exists x.
  exact B.
Qed.

Lemma p2:
  forall (D:Set) (a:D->Prop) (b:D->Prop),
  (forall (x:D), a x) /\ (forall (x:D), b x)
  -> (forall (x:D), a x /\ b x).
  intros.
  destruct H as [A B].
  specialize (A x).
  specialize (B x).
  apply conj.
  exact A.
  exact B.
Qed.


Lemma p3:
  forall (D:Set) (a:D->Prop) (b:D->Prop),
  (forall (x:D), a x) \/ (forall (x:D), b x)
  -> (forall (x:D), a x \/ b x).
  intros.
  destruct H.
  specialize (H x).
  left.
  assumption.
  specialize (H x).
  right.
  assumption.
Qed.

