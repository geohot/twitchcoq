Inductive nat' : Set :=
  | zero : nat'
  | succ : nat' -> nat'.

(** This isn't true for x = 0! **)
Theorem all_have_succ : forall x : nat', exists y : nat', x = (succ y).
Abort.

Theorem all_have_succ_real : forall x : nat', exists y : nat', (succ x) = y.
  intros x.
  exists (succ x).
  reflexivity.
Qed.

