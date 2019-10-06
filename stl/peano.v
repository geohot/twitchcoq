(** this makes intros work *)
Declare ML Module "ltac_plugin".
Set Default Proof Mode "Classic".

(** False has no items *)
Inductive False : Prop :=.

(** True has one item *)
Inductive True : Prop := I : True.

(** bool and nat have two items *)
Inductive bool' : Set :=
  | true : bool'
  | false : bool'.

Inductive nat' : Set :=
  | zero : nat'
  | succ : (forall (_ : nat'), nat').

Inductive eqb' (x : bool') : (forall (_ : bool'), Type) := eqb'_refl : eqb' x x.
Inductive eqn' (x : nat') : (forall (_ : nat'), Type) := eqn'_refl : eqn' x x.

Definition andb' (b1 b2 : bool') : bool' := if b1 then b2 else false.
Definition orb' (b1 b2 : bool') : bool' := if b1 then true else b2.
Definition notb' (b1 : bool') : bool' := if b1 then false else true.

(** note, exists is hard to make work *)
(**Theorem all_have_succ : forall x : nat', exists y : nat', eqn' (succ x) y.
Proof.
  intros x.
  exists (succ x).
  reflexivity.
Abort.*)

Theorem demorgan : forall a b : bool', eqb' (notb' (orb' a b)) (andb' (notb' a) (notb' b)).
Proof.
  intros a b.
  destruct a; destruct b; simpl; reflexivity.
Qed.

