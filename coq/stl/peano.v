(** this makes intros work *)
Declare ML Module "ltac_plugin".
Set Default Proof Mode "Classic".

(** annoying without this *)
Reserved Notation "x -> y" (at level 99, right associativity, y at level 200).

(** for all x of type T, P *)
(** the variable in the forall is _, so this is a non dependent product *)
Notation "A -> B" := (forall _ : A, B).

(** unit/empty is like True/False, but it's a Set, not a Prop *)
(**Inductive unit : Set := tt.
Inductive empty : Set :=.*)

(** bool has two items *)
(** the bool' was impiled on the type of the items *)
Inductive bool' : Set :=
  | true : bool'
  | false : bool'.

(** False has no items *)
Inductive False : Prop :=.
Definition not (A:Prop) := A -> False.

(** True has one item *)
Inductive True : Prop := I : True.

(** Prop is better than Type *)
Inductive eqb' (x : bool') : bool' -> Prop :=
  | eqb'_refl : eqb' x x.

Theorem true_is_true : eqb' true true.
Proof.
  exact (eqb'_refl true).
Qed.

Definition check (e : bool') : Prop :=
  match e with
  | true => True
  | false => False
  end.

Theorem true_is_not_false : not (eqb' true false).
Proof.
  exact (eqb'_ind true check I false).
Qed.

Theorem false_implies_true : False -> True.
Proof.
  intros.
  induction H.
Qed.

Theorem true_not_implies_false : not (True -> False).
Proof.
  unfold not.
  intros.
  assert True.
  exact I.
  apply H in H0.
  apply H0.
Qed.


(** print the theorems *)
Print true_is_true.
Print true_is_not_false.
Print false_implies_true.

(** can we prove to here in twitchcoq? CHALLENGE *)

(**Inductive nat' : Set :=
  | zero : nat'
  | succ : nat' -> nat'.


Definition eqb'' (x y : bool') := match x,y with
  | true, true => True
  | false, false => True
  | _, _ => False
end.

Inductive eqn' (x : nat') : nat' -> Prop :=
  | eqn'_refl : eqn' x x.

Definition andb' (b1 b2 : bool') : bool' :=
  match b1 with
  | true => b2
  | false => false
  end.
Definition orb' (b1 b2 : bool') : bool' :=
  match b1 with
  | true => true
  | false => b2
  end.
Definition notb' (b1 : bool') : bool' :=
  match b1 with
  | true => false
  | false => true
  end.
*)

(**Theorem demorgan : forall a b : bool', eqb' (notb' (orb' a b)) (andb' (notb' a) (notb' b)).
Proof.
  intros a b.
  destruct a; destruct b; simpl; reflexivity.
Qed.*)

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


