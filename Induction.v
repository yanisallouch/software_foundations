Theorem add_0_r_firsttry : forall n:nat,
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
  (* FILL IN HERE *) intros. induction n as [|n' IHn'].  simpl. induction m. reflexivity. simpl. rewrite <- IHm. reflexivity.
  - induction m. 

Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.

Proof.
  (* FILL IN HERE *) Admitted.