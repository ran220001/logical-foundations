From LF Require Export A_Basics.

Theorem add_0_r_firsttry : forall n:nat,
  n + 0 = n.

Proof.
  intros n.
  simpl. (* Does nothing! *)
Abort.

Theorem add_0_r_secondtry : forall n:nat,
  n + 0 = n.
Proof.
  intros n. destruct n as [|n'] eqn:E.
  - (* n = 0 *)
    reflexivity. (* so far so good... *)
  - (* n = S n' *)
    simpl. (* ...but here we are stuck again *)
Abort.

Theorem add_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem minus_n_n : forall n,
  minus n n = 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)
    reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity. Qed.

(* Exercise 1: basic_induction *)

Theorem mul_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m. induction n as [| n' IHn'].
  - simpl. (* redundant, but useful for visualisation *)
    rewrite -> add_0_r. reflexivity.
  - simpl. rewrite <- plus_n_Sm. rewrite -> IHn'. reflexivity. Qed.

Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity. Qed.

(* End of exercise 1 *)

(* Exercise 2: double_plus *)

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n .
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite <- plus_n_Sm.
    rewrite -> IHn'. reflexivity. Qed.

(* End of exercise 2 *)

(* Exercise 3: eqb_refl *)

Theorem eqb_refl : forall n : nat,
  (n =? n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity. Qed.

(* End of exercise 3 *)

(* Exercise 4: even_S (optional) *)

Theorem even_S : forall n : nat,
  even (S n) = negb (even n).
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - rewrite -> IHn'. rewrite -> negation_fn_applied_twice.
    + reflexivity.
    + reflexivity. Qed.

(* End of exercise 4 *)