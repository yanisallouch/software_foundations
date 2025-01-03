Theorem add_0_r_firsttry : forall n:nat,
  n + 0 = n.
Proof. induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem add_0_r : forall n:nat,
  n + 0 = n.
Proof. induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem mul_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  (* FILL IN HERE *) induction n. reflexivity. simpl. rewrite IHn. reflexivity.
Qed.
 
Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  (* FILL IN HERE *) induction n. 
- intros. simpl. reflexivity.
- intros. simpl. rewrite IHn. reflexivity.
Qed.
Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
  (* FILL IN HERE *)
  intros. induction n as [| n' IHn].
  - (* Base case: n = 0 *)
      simpl. (* 0 + m = m by definition *)
      rewrite add_0_r. (* m + 0 = m by definition ofadd_comm Nat.add_0_r *)
      reflexivity.
  -
      simpl.
      rewrite IHn.
      rewrite plus_n_Sm.
      reflexivity.
Qed.

Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  (* FILL IN HERE *)
  intros. induction n as [| n' IHn'].
  -
      simpl.
      reflexivity.
  - 
      simpl.
      rewrite IHn'.
      reflexivity.
Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n .
Proof.
  (* FILL IN HERE *)
  intros. induction n as [|n' IHn'].
  -
    simpl. reflexivity.
  -
    simpl. rewrite IHn'.
    rewrite plus_n_Sm.
    reflexivity.
Qed.

Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.

Theorem eqb_refle : forall n : nat, (eqb n n) = true.
Proof.
  intros.
  induction n as [|n' IHn']. simpl. reflexivity.
  simpl. rewrite IHn'. reflexivity.
Qed.

Fixpoint even (n : nat) : bool :=
  match n with
  | O => true
  | (S 0) => false
  | S (S m) => even m
  end.

Theorem even_S : forall n : nat,
  even (S n) = negb (even n).
Proof.
  intros n. induction n as [|n' IHn'].
  - (* Base case: n = 0 *)
    simpl. reflexivity.
  - (* Inductive step: n = S n' *)
    simpl. simpl in IHn'. rewrite IHn'. destruct n' as [|n''].
  + simpl. reflexivity.
  + simpl. simpl in IHn'. rewrite <- IHn'. 
Admitted.

Theorem mult_0_plus' : forall n m : nat,
  (n + 0 + 0) * m = n * m.
Proof.
  intros n m.
  assert (H: n + 0 + 0 = n).
    { rewrite add_comm. simpl. rewrite add_comm. reflexivity. }
  rewrite H.
  reflexivity. Qed.

Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  (* We just need to swap (n + m) for (m + n)... seems
     like add_comm should do the trick! *)
  rewrite add_comm.
  (* Doesn't work... Coq rewrites the wrong plus! :-( *)
Abort.

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite add_comm. reflexivity. }
  rewrite H. reflexivity. Qed.

Theorem add_shuffle3 : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  (* FILL IN HERE *) 
  intros.
  rewrite <- add_assoc.