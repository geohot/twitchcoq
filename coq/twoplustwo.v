Inductive nat' : Set :=
  | Z : nat'
  | S : nat' -> nat'.

Inductive eqn' (x : nat') : nat' -> Prop :=
  | eqn'_refl : eqn' x x.

Theorem one_ne_zero : eqn' (S Z) Z -> False.
Proof.
  intros.
  inversion H.
Qed.

Fixpoint plus' (x y : nat') : nat' :=
  match x with
  | Z => y
  | S w => S (plus' w y)
  end.

Theorem two_plus_two_eq_four : eqn' (plus' (S (S Z)) (S (S Z))) (S (S (S (S Z)))).
Proof.
  apply eqn'_refl.
Qed.

