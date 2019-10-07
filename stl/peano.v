(** this makes intros work *)
Declare ML Module "ltac_plugin".
Set Default Proof Mode "Classic".

(** annoying without this *)
Reserved Notation "x -> y" (at level 99, right associativity, y at level 200).
Notation "A -> B" := (forall (_ : A), B).

(** bool has two items *)
Inductive bool' : Set :=
  | true : bool'
  | false : bool'.

(** False has no items *)
Inductive False : Prop :=.

(** True has one item *)
Inductive True : Prop := I : True.

Definition not (A:Prop) := A -> False.

Inductive nat' : Set :=
  | zero : nat'
  | succ : nat' -> nat'.

(** Prop is better than Type *)
Inductive eqb' (x : bool') : bool' -> Prop :=
  | eqb'_refl : eqb' x x.

Definition eqb'' (x y : bool') := match x,y with
  | true, true => True
  | false, false => True
  | _, _ => False
end.

Inductive eqn' (x : nat') : nat' -> Prop :=
  | eqn'_refl : eqn' x x.

Definition andb' (b1 b2 : bool') : bool' := if b1 then b2 else false.
Definition orb' (b1 b2 : bool') : bool' := if b1 then true else b2.
Definition notb' (b1 : bool') : bool' := if b1 then false else true.

Theorem true_is_true : eqb' true true.
Proof.
  reflexivity.
Qed.

Theorem demorgan : forall a b : bool', eqb' (notb' (orb' a b)) (andb' (notb' a) (notb' b)).
Proof.
  intros a b.
  destruct a; destruct b; simpl; reflexivity.
Qed.

(**Theorem eqb_is_good : forall x y : bool', (eqb'' x y) -> (eqb' x y).
Proof.
  intros.
  destruct x.
    destruct y.
      reflexivity.
      unfold eqb'' in H.
      contradiction.
    destruct y.
      unfold eqb'' in H.
      contradiction.
      reflexivity.
Qed.

Theorem eqb_is_also_good : forall x y : bool', (eqb' x y) -> (eqb'' x y).
Proof.
  intros.
  destruct x; destruct y.
  reflexivity.
  unfold eqb''.*)

Definition check (e : bool') : Prop :=
  match e with
  | true => True
  | false => False
  end.

Theorem true_is_not_false : not (eqb' true false).
Proof.
  intros H.
  exact (eqb'_ind true check I false H).
Qed.

(**
  specialize (eqb'_ind true).
  intros.
  specialize (eqb'_ind true (fun e : bool' => e)).
  assert (eqb' true true).
    reflexivity.
  specialize (bool'_ind (eqb' true)).
  intros.
Abort.

Theorem dummy : forall b : bool', eqb' true b -> False.
Proof.
*)


(**
  intros.
  inversion H.
Qed.*)

(** note, exists is hard to make work *)
(**Theorem all_have_succ : forall x : nat', ex (eqn' (succ x) y).
Proof.
  intros x.
  exists (succ x).
  reflexivity.
Qed.
*)


