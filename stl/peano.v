Inductive bool' : Set :=
  | true : bool'
  | false : bool'.

Definition andb' (b1 b2 : bool') : bool' := if b1 then b2 else false.
Definition orb' (b1 b2 : bool') : bool' := if b1 then true else b2.
Definition notb' (b1 : bool') : bool' := if b1 then false else true.

Inductive nat' : Set :=
  | zero : nat'
  | succ : nat' -> nat'.

Theorem all_have_succ : forall x : nat', exists y : nat', (succ x) = y.
Proof.
  intros x.
  exists (succ x).
  reflexivity.
Qed.

Theorem demorgan : forall a b : bool', notb' (orb' a b) = andb' (notb' a) (notb' b).
Proof.
  intros a b.
  (** prove all four of the cases *)
  destruct a; destruct b; simpl; reflexivity.
Qed.


