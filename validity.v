
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