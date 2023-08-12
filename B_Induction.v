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

(* Exercise 5: destruct_induction (optional) *)

(*
The difference between the tactics `destruct` and `induction`:
While both tactics deconstruct their variables and generate several subgoals,
`induction` also provides an induction hypothesis.
*)

(* End of exercise 5 *)

Theorem mult_0_plus' : forall n m : nat,
  (n + 0 + 0) * m = n * m.
Proof.
  intros n m.
  assert (H: n + 0 + 0 = n).
    { rewrite add_comm. simpl. rewrite add_comm. reflexivity. }
  rewrite -> H.
  reflexivity. Qed.

Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  rewrite add_comm.
Abort.

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite add_comm. reflexivity. }
  rewrite H. reflexivity. Qed.

Theorem add_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof. intros n m p. induction n as [| n' IHn']. reflexivity.
  simpl. rewrite IHn'. reflexivity. Qed.

Theorem add_assoc'' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n' IHn'].
  - (* n = 0 *)
    reflexivity.
  - (* n = S n' *)
    simpl. rewrite IHn'. reflexivity. Qed.

(* Exercise 6: add_comm_informal *)

(*
Theorem: Addition is commutative.

Proof: Let there be any n and m. We must prove that n + m = m + n.
We will prove this by induction on n.
First, suppose n = 0. We must show that
  0 + m = m + 0.
By the definition of +, we have
  m = m + 0.
Using the theorem n + 0 = n, we have
  m = m.
Therefore, 0 + m = m + 0.

Next, suppose n = S n', where
  n' + m = m + n'.
We must now show that
  (S n') + m = m + (S n').
By the definition of +, we have
  S (n' + m) = m + (S n').
Using the theorem S (n + m) = n + (S m), we have
  S (n' + m) = S (m + n').
Rewriting using the induction hypothesis, we get
  S (n' + m) = S (n' + m). Qed.
*)

(* Do not modify the following line: *)
Definition manual_grade_for_add_comm_informal : option (nat*string) := None.

(* End of exercise 6 *)

(* Exercise 7: eqb_refl_informal *)

(*
Theorem: (n =? n) = true for any n.

Proof: By induction on n.
First, suppose n = 0. We must show that
  (0 =? 0) = true.
This follows directly from the definition of =?.

Next, suppose n = S n', where
  (n' =? n') = true.
We must now show that
  (S n' =? S n') = true.
By the definition of natural numbers, this follows from
  (n' =? n') = true,
which is immediate from the induction hypothesis. Qed.
*)

(* Do not modify the following line: *)
Definition manual_grade_for_eqb_refl_informal : option (nat*string) := None.

(* End of exercise 7 *)