(*
  Discrete Structures, Logic, and Computabilty. 3rd edition.
*)


Variable p : Empty_set -> Prop.

Lemma it_is_valid_if_D_is_not_empty:
  ~(forall (D : Set) (p : D -> Prop),
     ((forall x : D, p(x)) -> (exists x : D, p(x)))).
  intros contra.
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


Lemma p4:
  forall (D:Set) (a:D->Prop) (b:D->Prop),
  (forall (x:D), a x -> b x)
  -> (exists (x:D), a x) -> (exists (x:D), b x).
  intros.
  destruct H0.
  specialize (H x).
  exists x.
  apply H.
  apply H0.
Qed.

Lemma p5:
  forall (D:Set) (a:D->Prop) (b:D->Prop),
  (forall (x:D), a x -> b x)
  -> ((exists (x:D), a x) -> (exists (x:D), b x)).
  intros.
  destruct H0.
  specialize (H x).
  exists x.
  apply H.
  apply H0.
Qed.


Variable a' : Empty_set -> Prop.
Variable b' : Empty_set -> Prop.

Lemma p6:
  ~forall (D:Set) (a:D->Prop) (b:D->Prop),
  (forall (x:D), (a x) -> (b x))
  -> ((forall (x:D), a x) -> (exists (x:D), b x)).
  intros contra.
  specialize (contra Empty_set a' b').
  destruct contra.
  Inductive p' : Empty_set -> Prop := .
  assert (Empty_set_ind' := Empty_set_ind (fun x : Empty_set => a' x -> b' x)).
  apply Empty_set_ind'.
  apply Empty_set_ind.
  contradiction x.
Qed.

Lemma p7:
  forall (D:Set) (a:D->Prop) (b:D->Prop),
  (forall (x:D), (a x) -> (b x))
  -> ((forall (x:D), a x) -> (forall (x:D), b x)).
  intro.
  intro.
  intro.
  intro.
  intro.
  intro.
  specialize (H0 x).
  specialize (H x).
  apply (H H0).Qed.


Lemma n1: ~
  exists (D:Set), exists (p : D->Prop), exists (c : D), ((p c) /\ ~(p c)).
  unfold not.
  intros contra.
  destruct contra.
  destruct (H) as [p].
  destruct (H0) as [c].
  clear H.
  clear H0.
  destruct H1 as [a b].
  apply b.
  exact a.
Qed.

Lemma n2: ~
  exists (D:Set) (p : D -> Prop),
  exists (x : D), ((p x) /\ ~(p x)).
  intros contra.
  destruct contra as [D].
  destruct H as [p].
  destruct H as [x].
  destruct H as [a b].
  apply (b a).
Qed.

Lemma n3: ~
  exists (D:Set) (p : D -> D -> Prop),
  exists (x : D), forall (y : D), ((p x y) /\ ~(p x y)).
  intros contra.
  destruct contra as [D].
  destruct H as [p].
  destruct H as [x].
  specialize (H x).
  destruct H as [a b].
  apply (b a).
Qed.

