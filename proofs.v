(* Nahas_tutorial *)

(*
This is
a comment
*)

Theorem my_first_proof : (forall A : Prop, A -> A).
Proof.
  intros A.
  intros proof_of_A.
  exact proof_of_A.
Qed.

Theorem forward_small : (forall A B : Prop, A -> (A->B) -> B).
Proof.
 intros A.
 intros B.
 intros proof_of_A.
 intros A_implies_B.
 pose (proof_of_B := A_implies_B proof_of_A).
 exact proof_of_B.
Qed.

Theorem backward_small : (forall A B : Prop, A -> (A->B)->B).
Proof.
 intros A B.
 intros proof_of_A A_implies_B.
 refine (A_implies_B _).
   exact proof_of_A.
Qed.

Theorem backward_large : (forall A B C : Prop, A -> (A->B) -> (B->C) -> C).
Proof.
 intros A B C.
 intros proof_of_A A_implies_B B_implies_C.
 refine (B_implies_C _).
   refine (A_implies_B _).
     exact proof_of_A.
Qed.

Theorem backward_huge : (forall A B C : Prop, A -> (A->B) -> (A->B->C) -> C).
Proof.
 intros A B C.
 intros proof_of_A A_implies_B A_imp_B_imp_C.
 refine (A_imp_B_imp_C _ _).
   exact proof_of_A.
   refine (A_implies_B _).
     exact proof_of_A.
Qed.

Theorem forward_huge : (forall A B C : Prop, A -> (A->B) -> (A->B->C) -> C).
Proof.
 intros A B C.
 intros proof_of_A A_implies_B A_imp_B_imp_C.
 pose (proof_of_B := A_implies_B proof_of_A).
 pose (proof_of_C := A_imp_B_imp_C proof_of_A proof_of_B).
 exact proof_of_C.
Show Proof.
Qed.

Theorem True_can_be_proven : True.
  exact I.
Qed.

Theorem False_cannot_be_proven : ~False.
Proof.
  unfold not.
  intros proof_of_False.
  exact proof_of_False.
Qed.

Theorem False_cannot_be_proven__again : ~False.
Proof.
  intros proof_of_False.
  case proof_of_False.
Qed.

Theorem thm_true_imp_true : True -> True.
Proof.
  intros proof_of_True.
  exact I.
Qed.

Theorem thm_false_imp_true : False -> True.
Proof.
  intros proof_of_False.
  exact I. 
Qed.

Theorem thm_false_imp_false : False -> False.
Proof.
  intros proof_of_False.
  case proof_of_False. 
Qed.

Theorem thm_true_imp_false : ~(True -> False).
Proof.
  intros T_implies_F.
  refine (T_implies_F _).
    exact I.
Qed.

Theorem absurd2 : forall A C : Prop, A -> ~ A -> C.
Proof.
  intros A C.
  intros proof_of_A proof_that_A_cannot_be_proven.
  unfold not in proof_that_A_cannot_be_proven.
  pose (proof_of_False := proof_that_A_cannot_be_proven proof_of_A).
  case proof_of_False.
Qed.

Require Import Bool.

Theorem true_is_True: Is_true true.
Proof.
  simpl.
  exact I.
Qed.

Theorem not_eqb_true_false: ~(Is_true (eqb true false)).
Proof.
  simpl.
  exact False_cannot_be_proven.
Qed.

Theorem eqb_a_a : (forall a : bool, Is_true (eqb a a)).
Proof.
  intros a.
  case a.
    simpl.
      exact I.
    simpl.
      exact I.
Qed.

Theorem thm_eqb_a_t: (forall a:bool, (Is_true (eqb a true)) -> (Is_true a)).
Proof.
  intros a.
  case a.

    simpl.
      intros proof_of_True.
      exact I.
    simpl.
        intros proof_of_False.
        case proof_of_False.
Qed.

Theorem left_or : (forall A B : Prop, A -> A \/ B).
Proof.
  intros A B.
  intros proof_of_A.
  pose (proof_of_A_or_B := or_introl proof_of_A : A \/ B).
  exact proof_of_A_or_B.
Qed.

Theorem right_or : (forall A B : Prop, B -> A \/ B).
Proof.
  intros A B.
  intros proof_of_B.
  refine (or_intror _).
    exact proof_of_B.
Qed.

Theorem or_commutes : (forall A B, A \/ B -> B \/ A).
Proof.
  intros A B.
  intros A_or_B.
  case A_or_B.
    intros proof_of_A.
        refine (or_intror _).
          exact proof_of_A.
    intros proof_of_B.
        refine (or_introl _).
          exact proof_of_B.
Qed.

Theorem both_and : (forall A B : Prop, A -> B -> A /\ B).
Proof.
  intros A B.
  intros proof_of_A proof_of_B.
  refine (conj _ _).
    exact proof_of_A.

    exact proof_of_B.
Qed.

Theorem and_commutes : (forall A B, A /\ B -> B /\ A).
Proof.
  intros A B.
  intros A_and_B.
  case A_and_B.
    intros proof_of_A proof_of_B.
      refine (conj _ _).
        exact proof_of_B.

        exact proof_of_A.
Qed.

Theorem and_commutes__again : (forall A B, A /\ B -> B /\ A).
Proof.
  intros A B.
  intros A_and_B.
  destruct A_and_B as [ proof_of_A proof_of_B].
  refine (conj _ _).
    exact proof_of_B.

    exact proof_of_A.
Qed.

Theorem orb_is_or : (forall a b, Is_true (orb a b) <-> Is_true a \/ Is_true b).
Proof.
  intros a b.
  unfold iff.
  refine (conj _ _).
    intros H.
        case a, b.
          simpl.
                refine (or_introl _).
                  exact I.
          simpl.
                exact (or_introl I).
          exact (or_intror I).
          simpl in H.
                case H.
          intros H.
              case a, b.
          simpl.
                exact I.
          exact I.
          exact I.
          case H.
          intros A.
                   simpl in A.
                   case A.
          intros B.
                   simpl in B.
                   case B.
Qed.

Theorem andb_is_and : (forall a b, Is_true (andb a b) <-> Is_true a /\ Is_true b).
Proof.
  intros a b.
  unfold iff.
  refine (conj _ _).
  intros H.
      case a, b.
        simpl.
              exact (conj I I).
(* je suis pas sur de suivre les raisonnements suivant*)
        simpl in H.
              case H.
        simpl in H.
              case H.
        simpl in H.
              case H.
(* jusqu'ici *)
        intros H.
            case a,b.
        simpl.
              exact I.
        simpl in H.
              destruct H as [ A B].
              case B.
        simpl in H.
              destruct H as [ A B].
              case A.
        simpl in H.
              destruct H as [ A B].
              case A.
Qed.

Theorem negb_is_not1 : (forall a, Is_true (negb a) <-> (~(Is_true a))).
Proof.
  intros a.
  unfold iff.
  refine (conj _ _).
  - (* First subgoal *)
    intros H_true.
    destruct a.
  -- (* First subsubgoal *)
      simpl in H_true.
        intros A.
        exact H_true.
  -- (* Second subsubgoal *)
      simpl.
        intros A.
        exact A.
 - (* Second subgoal *)
      intros H_true.
        destruct a.
  -- (* First subsubgoal *)
          simpl in H_true.
            simpl.
            refine (H_true _).
            exact I.
  -- (* Second subsubgoal *)
          simpl.
           exact I.
Qed.

Theorem negb_is_not : (forall a, Is_true (negb a) <-> (~ (Is_true a))).
Proof.
  intros a.
  unfold iff.
  refine (conj _ _).
  - (* Is_true (negb a) -> ~ Is_true a *)
    intros H H_true.
    destruct a.
    + (* Case: a = true *)
      simpl in H. (* Is_true false, which is False *)
      exact H.
    + (* Case: a = false *)
      simpl in H_true. (* Is_true false, which is False *)
      exact H_true.
  - (* ~ Is_true a -> Is_true (negb a) *)
    intros H.
    destruct a.
    + (* Case: a = true *)
      simpl. (* negb true = false *)
      unfold not in H. (* H : Is_true true -> False *)
      pose (H I). (* Derive False from H *)
      exact f.
    + (* Case: a = false *)
      simpl. (* negb false = true *)
      exact I.
Qed.

Definition basic_predicate
:=
  (fun a => Is_true (andb a true))
.


Theorem thm_exists_basics : (ex basic_predicate).
Proof.
  pose (witness := true).
  refine (ex_intro basic_predicate witness _).
    simpl.
    exact I.
Qed.

Theorem thm_exists_basics__again : (exists a, Is_true (andb a true)).
Proof.
  pose (witness := true).
  refine (ex_intro _ witness _).
  simpl.
  exact I.
Qed.

Theorem thm_forall_exists : (forall b, (exists a, Is_true(eqb a b))).
Proof.
  intros b.
  case b.
  pose (witness := true).
    refine (ex_intro _ witness _).
      simpl.
      exact I.
  pose (witness := false).
      refine (ex_intro _ witness _).
        simpl.
        exact I.
Qed.

Theorem thm_forall_exists__again : (forall b, (exists a, Is_true(eqb a b))).
Proof.
  intros b.
  refine (ex_intro _ b _).
  exact (eqb_a_a b).
Qed.

Theorem forall_exists : (forall P : Set->Prop,  (forall x, ~(P x)) -> ~(exists x, P x)).
Proof.
  intros P.
  intros forall_x_not_Px.
  intros exists_x_Px.
  destruct exists_x_Px as [ witness proof_of_Pwitness].
  pose (not_Pwitness := forall_x_not_Px witness).
  unfold not in not_Pwitness.
  pose (proof_of_False := not_Pwitness proof_of_Pwitness).
  case proof_of_False.
Qed.

Theorem exists_forall : (forall P : Set->Prop,  ~(exists x, P x) -> (forall x, ~(P x))).
Proof.
  intros P.
  intros not_exists_x_Px.
  intros x.
  intros P_x.
  unfold not in not_exists_x_Px.
  refine (not_exists_x_Px _).
    exact (ex_intro P x P_x).
Qed.

Theorem thm_eq_sym : (forall x y : Set, x = y -> y = x).
Proof.
  intros x y.
  intros x_y.
  destruct x_y as [].
  exact (eq_refl x).
Qed.

Theorem thm_eq_trans : (forall x y z: Set, x = y -> y = z -> x = z).
Proof.
  intros x y z.
  intros x_y y_z.
  destruct x_y as [].
  destruct y_z as [].
  exact (eq_refl x).
Qed.

Theorem thm_eq_trans__again : (forall x y z: Set, x = y -> y = z -> x = z).
Proof.
  intros x y z.
  intros x_y y_z.
  rewrite x_y.
  rewrite <- y_z.
  exact (eq_refl y).
Qed.

Theorem andb_sym : (forall a b, a && b = b && a).
Proof.
  intros a b.
  case a, b.
simpl.
    exact (eq_refl true).
simpl.
    exact (eq_refl false).
simpl.
    exact (eq_refl false).
simpl.
    exact (eq_refl false).
Qed.

Theorem neq_nega: (forall a, a <> (negb a)).
Proof.
  intros a.
  unfold not.
  case a.
    intros a_eq_neg_a.
    simpl in a_eq_neg_a.
    discriminate a_eq_neg_a.


    intros a_eq_neg_a.
    simpl in a_eq_neg_a.
    discriminate a_eq_neg_a.
Qed.

Theorem plus_2_3 : (S (S O)) + (S (S (S O))) = (S (S (S (S (S O))))).
Proof.
  simpl.
  exact (eq_refl 5).
Qed.

Theorem plus_O_n : (forall n, O + n = n).
Proof.
  intros n.
  simpl.
  exact (eq_refl n).
Qed.

Theorem plus_n_O : (forall n, n + O = n).
Proof.
  intros n.
  elim n.
simpl.
    exact (eq_refl O).
intros n'.
    intros inductive_hypothesis.
    simpl.
    rewrite inductive_hypothesis.
    exact (eq_refl (S n')).
Qed.

Theorem plus_n_O__again : (forall n, n + O = n).
Proof.
  intros n.
  induction n as [|n' inductive_hypothesis].
simpl.
    exact (eq_refl O).
simpl.
    rewrite inductive_hypothesis.
    exact (eq_refl (S n')).
Qed.

Theorem or_commutes__again : (forall A B, A \/ B -> B \/ A).
Proof.
  intros A B.
  intros A_or_B.
  destruct A_or_B as [proof_of_A | proof_of_B].
refine (or_intror _).
      exact proof_of_A.
refine (or_introl _).
      exact proof_of_B.
Qed.

Print or.
Print nat_ind.

Theorem plus_sym: (forall n m, n + m = m + n).
Proof.
  intros.
  elim n.
  elim m.
    simpl.
      exact eq_refl.
    intros.
      simpl.
      rewrite <- H.
      simpl.
      exact (eq_refl (S n0)).
    intros.
    simpl.
    rewrite H.
    elim m.
    simpl.
    exact eq_refl.
    intros.
    simpl.
    rewrite H0.
    exact eq_refl.
Qed.

Theorem minus_is_funny : (0 - 1) = (0 - 2).
Proof.
  simpl.
  exact (eq_refl 0).
Qed.

From Coq Require Import List.

Theorem cons_adds_one_to_length :
   (forall A:Type,
   (forall (x : A) (lst : list A),
   length (x :: lst) = (S (length lst)))).
Proof.
  intros.
  simpl.
  exact eq_refl.
Qed.

Definition hd (A : Type) (default : A) (l : list A)
:=
  match l with
    | nil => default
    | x :: _ => x
  end.

Definition my_hd_for_nat_lists
:=
  hd nat 0.

Compute my_hd_for_nat_lists nil.
Compute my_hd_for_nat_lists (5 :: 4 :: nil).

Theorem correctness_of_hd :
   (forall A:Type,
   (forall (default : A) (x : A) (lst : list A),
   (hd A default nil) = default /\ (hd A default (x :: lst)) = x)).
Proof.
  intros.
  refine (conj _ _).
  simpl.
  exact eq_refl.
  simpl.
  exact eq_refl.
Qed.

Definition hd_error (A : Type) (l : list A)
:=
  match l with
    | nil => None
    | x :: _ => Some x
  end.

Compute hd_error nat nil.
Compute hd_error nat (5 :: 4 :: nil).

Theorem correctness_of_hd_error :
   (forall A:Type,
   (forall (x : A) (lst : list A),
   (hd_error A nil) = None /\ (hd_error A (x :: lst)) = Some x)).
Proof.
  intros.
  refine (conj _ _).
  simpl.
  exact eq_refl.
  simpl.
  exact eq_refl.
Qed.

Definition hd_never_fail (A : Type) (lst : list A) (safety_proof : lst <> nil)
  : A
:=
  (match lst as b return (lst = b -> A) with
    | nil =>    (fun foo : lst = nil =>
                   match (safety_proof foo) return A with
                   end
                )
    | x :: _ => (fun foo : lst = x :: _ =>
                   x
                )
  end) eq_refl.

Theorem correctness_of_hd_never_fail :
   (forall A:Type,
   (forall (x : A) (rest : list A),
   (exists safety_proof : ((x :: rest) <> nil),
      (hd_never_fail  A (x :: rest) safety_proof) = x))).
Proof.
  intros.
    assert (witness : ((x :: rest) <> nil)).
    unfold not.
    intros.
      discriminate H.
    refine (ex_intro _ witness _).
    simpl.
    exact eq_refl.
Qed.

Definition tl (A : Type) (l:list A) :=
  match l with
    | nil => nil
    | a :: m => m
  end.

Definition tl_error (A : Type) (l : list A)
  : option (list A)
:=
  match l with
    | nil => None
    | _ :: x => Some x
  end.

Definition tl_never_fail (A : Type) (lst : list A) (safety_proof : lst <> nil)
  : list A :=
 match lst as l return (l <> nil -> list A) with
  | nil => fun safety_proof => match safety_proof eq_refl with end
  | _ :: t => fun _ => t
  end safety_proof.

Theorem hd_tl :
   (forall A:Type,
   (forall (default : A) (x : A) (lst : list A),
   (hd A default (x::lst)) :: (tl A (x::lst)) = (x :: lst))).
Proof.
  intros.
  simpl.
  exact (eq_refl (x::lst)).
Qed.

Theorem app_nil_l :
  forall (A : Type) (l : list A), nil ++ l = l.
Proof.
intros.
simpl.
exact eq_refl.
Qed.

Theorem app_nil_r : (forall A:Type, (forall l:list A, forall l:list A, l ++ nil = l)).
Proof.
  intros.
  elim l0.
  simpl.
  exact eq_refl.
  intros.
  simpl.
  rewrite H.
  exact eq_refl.
Qed.

Theorem app_comm_cons : forall A (x y:list A) (a:A), a :: (x ++ y) = (a :: x) ++ y.
Proof.
  intros.
  simpl.
  exact eq_refl.
Qed.

Theorem app_assoc : forall A (l m n:list A), l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros.
  elim l.
  simpl.
  exact  eq_refl.
  intros.
  simpl.
  rewrite <- H.
  exact eq_refl.
Qed.

Theorem app_cons_not_nil : forall A (x y:list A) (a:A), nil <> x ++ a :: y.
Proof.
  intros.
  unfold not.
  elim x.
  simpl.
  intros.
  discriminate H.
  intros.
  discriminate H0.
Qed.

(* Software Foundations manual *)
(* Chapter 1 : Basics *)

Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.
  
  Compute (next_weekday friday).
(* ==> monday : day *)
  Compute (next_weekday (next_weekday saturday)).
(* ==> tuesday : day *)

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.
Proof. simpl. reflexivity. Qed.

From Coq Require Export String.

Inductive bool : Type :=
  | true
  | false.

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4: (orb true true) = true.
Proof. simpl. reflexivity. Qed.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).
Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.

Definition negb' (b:bool) : bool :=
  if b then false
  else true.
Definition andb' (b1:bool) (b2:bool) : bool :=
  if b1 then b2
  else false.
Definition orb' (b1:bool) (b2:bool) : bool :=
  if b1 then true
  else b2.

Definition nandb (b1:bool) (b2:bool) : bool :=
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
  match b1, b2 with
  | false, false => true
  | false, true => true
  | true, false => true
  | true, true => false
  end.

Compute nandb true true.   (* Expected: false *)
Compute nandb true false.  (* Expected: true *)
Compute nandb false true.  (* Expected: true *)
Compute nandb false false. (* Expected: true *)

Example test_nandb1: (nandb true false) = true.
(* FILL IN HERE *)
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
(* FILL IN HERE *) Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
(* FILL IN HERE *) Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
(* FILL IN HERE *) Proof. simpl. reflexivity. Qed.

Check true.
(* ===> true : bool *)
Check true
  : bool.
Check (negb true)
  : bool.
Check negb
  : bool -> bool.

Inductive rgb : Type :=
  | red
  | green
  | blue.
Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).

Definition monochrome (c : color) : bool :=
  match c with
  | black => true
  | white => true
  | primary p => false
  end.

Definition isred (c : color) : bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false
  end.

Module Playground.
  Definition foo : rgb := blue.
End Playground.

Definition foo : bool := true.
Check Playground.foo : rgb.
Check foo : bool.

Module TuplePlayground.

Inductive bit : Type :=
  | B1
  | B0.

Inductive nybble : Type :=
  | bits (b0 b1 b2 b3 : bit).

Check (bits B1 B0 B1 B0)
  : nybble.

Definition all_zero (nb : nybble) : bool :=
  match nb with
  | (bits B0 B0 B0 B0) => true
  | (bits _ _ _ _) => false
  end.

Compute (all_zero (bits B1 B0 B1 B0)).
(* ===> false : bool *)
Compute (all_zero (bits B0 B0 B0 B0)).
(* ===> true : bool *)
End TuplePlayground.

Module NatPlayground.

Inductive nat : Type :=
  | O
  | S (n : nat).

Inductive otherNat : Type :=
  | stop
  | tick (foo : otherNat).

Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S n' => n'
  end.

End NatPlayground.

Check (S (S (S (S O)))).

Definition minustwo (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.

Compute (minustwo 4).
(* ===> 2 : nat *)

Check S : nat -> nat.
Check pred : nat -> nat.
Check minustwo : nat -> nat.

Fixpoint even (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.

Definition odd (n:nat) : bool :=
  negb (even n).

Example test_odd1: odd 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_odd2: odd 4 = false.
Proof. simpl. reflexivity. Qed.

Module NatPlayground2.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Compute (plus 3 2).
(* ===> 5 : nat *)

(*      plus 3 2
   i.e. plus (S (S (S O))) (S (S O))
    ==> S (plus (S (S O)) (S (S O)))
          by the second clause of the match
    ==> S (S (plus (S O) (S (S O))))
          by the second clause of the match
    ==> S (S (S (plus O (S (S O)))))
          by the second clause of the match
    ==> S (S (S (S (S O))))
          by the first clause of the match
   i.e. 5  *)

Fixpoint mult (n m : nat) : nat :=
  match n with
  | O => O
  | S n' => plus m (mult n' m)
  end.
Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity. Qed.

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O , _ => O
  | S _ , O => n
  | S n', S m' => minus n' m'
  end.
  
(*      minus 3 2
   i.e. minus (S (S (S O))) (S (S O))
    ==> S (minus (S (S O)) (S (S O)))
          by the second clause of the match
    ==> S (S (plus (S O) (S (S O))))
          by the second clause of the match
    ==> S (S (S (plus O (S (S O)))))
          by the second clause of the match
    ==> S (S (S (S (S O))))
          by the first clause of the match
   i.e. 5  *)
Compute (minus 3 9).

End NatPlayground2.
Fixpoint exp (base power : nat) : nat :=
  match power with
  | O => S O
  | S p => mult base (exp base p)
  end.

Compute (exp 0 0).
Compute (exp 0 1).
Compute (exp 0 2).
Compute (exp 1 0).
Compute (exp 1 1).
Compute (exp 1 2).
Compute (exp 2 0).
Compute (exp 2 1).
Compute (exp 2 2).

Fixpoint factorial (n:nat) : nat :=
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
  match n with
  | O => 1
  | S n' => n * (factorial n')
  end.
  
Example test_factorial1: (factorial 3) = 6.
(* FILL IN HERE *) 
Proof. simpl. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
(* FILL IN HERE *)
Proof. simpl. reflexivity. Qed.

Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.
Check ((0 + 1) + 1) : nat.

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

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

Example test_leb1: leb 2 2 = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2: leb 2 4 = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3: leb 4 2 = false.
Proof. simpl. reflexivity. Qed.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.
Example test_leb3': (4 <=? 2) = false.
Proof. simpl. reflexivity. Qed.

Definition ltb (n m : nat) : bool :=
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
  match leb n m with
  | true =>   match leb m n with
              | true => false  (* If n <= m, we check if n is not equal to m *)
              | false => true           (* If n <= m, we check if n is not equal to m *)
              end
  | false => false         (* If n > m, then n is not less than m *)
  end.
Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.
Example test_ltb1: (ltb 2 2) = false.
(* FILL IN HERE *)
Proof. simpl. reflexivity. Qed.
Example test_ltb2: (ltb 2 4) = true.
(* FILL IN HERE *)
Proof. simpl. reflexivity. Qed.
Example test_ltb3: (ltb 4 2) = false.
(* FILL IN HERE *) 
Proof. simpl. reflexivity. Qed.

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity. Qed.

Theorem plus_O_n' : forall n : nat, 0 + n = n.
Proof.
  intros n. reflexivity. Qed.

Theorem plus_O_n'' : forall n : nat, 0 + n = n.
Proof.
  intros m. reflexivity. Qed.

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n. reflexivity. Qed.
Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
  intros n. reflexivity. Qed.

Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.
Proof. intros. rewrite <- H. reflexivity. Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  (* FILL IN HERE *)
  intros. rewrite H. rewrite <- H0. exact eq_refl. Qed.

Check mult_n_O.
(* ===> forall n : nat, 0 = n * 0 *)
Check mult_n_Sm.
(* ===> forall n m : nat, n * m + n = n * S m *)

Theorem mult_n_0_m_0 : forall p q : nat,
  (p * 0) + (q * 0) = 0.
Proof.
  intros p q.
  rewrite <- mult_n_O.
  rewrite <- mult_n_O.
  reflexivity. Qed.

Theorem mult_n_1 : forall p : nat,
  p * 1 = p.
Proof. intros. rewrite <- mult_n_Sm. rewrite <- mult_n_O. simpl. reflexivity. Qed.

Theorem plus_1_neq_0_firsttry : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n.
  simpl. (* does nothing! *)
Abort.

Theorem plus_1_neq_0 : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity. Qed.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b eqn:E.
  - reflexivity.
  - reflexivity. Qed.

Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
Qed.

Theorem andb_commutative' : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  { destruct c eqn:Ec.
    { reflexivity. }
    { reflexivity. } }
  { destruct c eqn:Ec.
    { reflexivity. }
    { reflexivity. } }
Qed.

Theorem andb3_exchange :
  forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof.
  intros b c d. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
  - destruct c eqn:Ec.
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
Qed.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  (* FILL IN HERE *)
  intros. destruct c.
  - reflexivity.
  - destruct b.
    -- exact H.
    -- exact H.
Qed.

Theorem plus_1_neq_0' : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity. Qed.

Theorem andb_commutative'' :
  forall b c, andb b c = andb c b.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
  0 =? (n + 1) = false.
Proof.
  (* FILL IN HERE *) 
  intros []. - reflexivity. - reflexivity.
Qed.

Fixpoint plus' (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus' n' m)
  end.

(*
Fixpoint plus' (n : nat) (m : nat) : nat :=
  match m with
  | O => m
  | S n' => S (plus' n' m)
  end.
*)

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  (* FILL IN HERE *) intros. destruct b. 
    - rewrite H. rewrite H. reflexivity.
    - rewrite H. rewrite H. reflexivity.
Qed.

Theorem negation_fn_applied_twice  :
  forall (f : bool -> bool),
  (forall (x : bool), f x = negb x) ->
  forall (b : bool), f (f b) = b.
Proof.
  (* FILL IN HERE *) intros. destruct b. 
    - rewrite H. rewrite H. reflexivity.
    - rewrite H. rewrite H. reflexivity.
Qed.

(* FILL IN HERE *)
(* Do not modify the following line: *)
Definition manual_grade_for_negation_fn_applied_twice : option (nat*string) := None.

Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  (* FILL IN HERE *) intros b c.
  destruct b eqn:Eb.
  destruct c eqn:Ec. simpl. reflexivity.
  simpl. intro. rewrite H. reflexivity.
  simpl. destruct c eqn:Ec.
  intro. exact H.
  intro. reflexivity.
Qed.

Module LateDays.

Inductive letter : Type :=
  | A | B | C | D | F.

Inductive modifier : Type :=
  | Plus | Natural | Minus.

Inductive grade : Type :=
  Grade (l:letter) (m:modifier).

Inductive comparison : Type :=
  | Eq (* "equal" *)
  | Lt (* "less than" *)
  | Gt. (* "greater than" *)

Definition letter_comparison (l1 l2 : letter) : comparison :=
  match l1, l2 with
  | A, A => Eq
  | A, _ => Gt
  | B, A => Lt
  | B, B => Eq
  | B, _ => Gt
  | C, (A | B) => Lt
  | C, C => Eq
  | C, _ => Gt
  | D, (A | B | C) => Lt
  | D, D => Eq
  | D, _ => Gt
  | F, (A | B | C | D) => Lt
  | F, F => Eq
  end.

Compute letter_comparison B A.
Compute letter_comparison D D.
Compute letter_comparison B F.

Theorem letter_comparison_Eq :
  forall l, letter_comparison l l = Eq.
Proof.
  (* FILL IN HERE *) intros. destruct l. reflexivity. reflexivity. reflexivity. reflexivity. reflexivity.
Qed.

Definition modifier_comparison (m1 m2 : modifier) : comparison :=
  match m1, m2 with
  | Plus, Plus => Eq
  | Plus, _ => Gt
  | Natural, Plus => Lt
  | Natural, Natural => Eq
  | Natural, _ => Gt
  | Minus, (Plus | Natural) => Lt
  | Minus, Minus => Eq
  end.

Definition grade_comparison (g1 g2 : grade) : comparison :=
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
  let (l1, m1) := g1 in
  let (l2, m2) := g2 in
  match letter_comparison l1 l2 with
  | Eq => modifier_comparison m1 m2
  | comparison => comparison
end.

Example test_grade_comparison1 :
(* FILL IN HERE *) 
  (grade_comparison (Grade A Minus) (Grade B Plus)) = Gt.
Proof. simpl. reflexivity. Qed.
Example test_grade_comparison2 :
  (grade_comparison (Grade A Minus) (Grade A Plus)) = Lt.
(* FILL IN HERE *) Proof. simpl. reflexivity. Qed.
Example test_grade_comparison3 :
  (grade_comparison (Grade F Plus) (Grade F Plus)) = Eq.
(* FILL IN HERE *) Proof. simpl. reflexivity. Qed.
Example test_grade_comparison4 :
  (grade_comparison (Grade B Minus) (Grade C Plus)) = Gt.
(* FILL IN HERE *) Proof. simpl. reflexivity. Qed.

Definition lower_letter (l : letter) : letter :=
  match l with
  | A => B
  | B => C
  | C => D
  | D => F
  | F => F (* Can't go lower than F! *)
  end.

Theorem lower_letter_lowers: forall (l : letter),
  letter_comparison (lower_letter l) l = Lt.
Proof.
  intros l.
  destruct l.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. (* We get stuck here. *)
Abort.

Theorem lower_letter_F_is_F:
  lower_letter F = F.
Proof.
  simpl. reflexivity.
Qed.

Theorem lower_letter_lowers:
  forall (l : letter),
    letter_comparison F l = Lt ->
    letter_comparison (lower_letter l) l = Lt.
Proof.
(* FILL IN HERE *) intros. destruct l. simpl. reflexivity. simpl. reflexivity. simpl. reflexivity. simpl. reflexivity. simpl. exact H.
Qed.

Definition lower_modifier (m : modifier) : modifier :=
  match m with
  | Plus => Natural
  | Natural => Minus
  | Minus => Minus
  end.

Definition lower_grade (g : grade) : grade :=
  let (l, m) := g in
  match m with
  | Plus => Grade l Natural
  | Natural => Grade l Minus
  | Minus =>
    match l with
    | A => Grade B Plus
    | B => Grade C Plus
    | C => Grade D Plus
    | D => Grade F Plus
    | F => Grade F Minus
    end
end.

Example lower_grade_A_Plus :
  lower_grade (Grade A Plus) = (Grade A Natural).
Proof.
(* FILL IN HERE *) simpl. reflexivity. Qed.
Example lower_grade_A_Natural :
  lower_grade (Grade A Natural) = (Grade A Minus).
Proof.
(* FILL IN HERE *) simpl. reflexivity. Qed.
Example lower_grade_A_Minus :
  lower_grade (Grade A Minus) = (Grade B Plus).
Proof.
(* FILL IN HERE *) simpl. reflexivity. Qed.
Example lower_grade_B_Plus :
  lower_grade (Grade B Plus) = (Grade B Natural).
Proof.
(* FILL IN HERE *) simpl. reflexivity. Qed.
Example lower_grade_F_Natural :
  lower_grade (Grade F Natural) = (Grade F Minus).
Proof.
(* FILL IN HERE *) simpl. reflexivity. Qed.
Example lower_grade_twice :
  lower_grade (lower_grade (Grade B Minus)) = (Grade C Natural).
Proof.
(* FILL IN HERE *) simpl. reflexivity. Qed.
Example lower_grade_thrice :
  lower_grade (lower_grade (lower_grade (Grade B Minus))) = (Grade C Minus).
Proof.
(* FILL IN HERE *) simpl. reflexivity. Qed.

Theorem lower_grade_F_Minus : lower_grade (Grade F Minus) = (Grade F Minus).
Proof.
(* FILL IN HERE *) simpl. reflexivity. Qed.

(* GRADE_THEOREM 0.25: lower_grade_A_Plus *)
(* GRADE_THEOREM 0.25: lower_grade_A_Natural *)
(* GRADE_THEOREM 0.25: lower_grade_A_Minus *)
(* GRADE_THEOREM 0.25: lower_grade_B_Plus *)
(* GRADE_THEOREM 0.25: lower_grade_F_Natural *)
(* GRADE_THEOREM 0.25: lower_grade_twice *)
(* GRADE_THEOREM 0.25: lower_grade_thrice *)
(* GRADE_THEOREM 0.25: lower_grade_F_Minus *)

Theorem lower_grade_lowers :
  forall (g : grade),
    grade_comparison (Grade F Minus) g = Lt ->
    grade_comparison (lower_grade g) g = Lt.
Proof.
  (* FILL IN HERE *) intros. destruct g. simpl. destruct m.
  - simpl. destruct l.  simpl. reflexivity.
  -- simpl. reflexivity.
  -- simpl. reflexivity.
  -- simpl. reflexivity.
  -- simpl. reflexivity.
  - destruct l.
  -- simpl. reflexivity.
  -- simpl. reflexivity.
  -- simpl. reflexivity.
  -- simpl. reflexivity.
  -- simpl. reflexivity.
  - destruct l.
  -- simpl. reflexivity.
  -- simpl. reflexivity.
  -- simpl. reflexivity.
  -- simpl. reflexivity.
  -- rewrite H. reflexivity.
Qed.

Definition apply_late_policy (late_days : nat) (g : grade) : grade :=
  if late_days <? 9 then g
  else if late_days <? 17 then lower_grade g
  else if late_days <? 21 then lower_grade (lower_grade g)
  else lower_grade (lower_grade (lower_grade g)).

Theorem apply_late_policy_unfold :
  forall (late_days : nat) (g : grade),
    (apply_late_policy late_days g)
    =
    (if late_days <? 9 then g else
       if late_days <? 17 then lower_grade g
       else if late_days <? 21 then lower_grade (lower_grade g)
            else lower_grade (lower_grade (lower_grade g))).
Proof.
  intros. reflexivity.
Qed.

Theorem no_penalty_for_mostly_on_time :
  forall (late_days : nat) (g : grade),
    (late_days <? 9 = true) ->
    apply_late_policy late_days g = g.
Proof.
  (* FILL IN HERE *) intros. unfold apply_late_policy. rewrite H. reflexivity.
Qed.

Theorem grade_lowered_once :
  forall (late_days : nat) (g : grade),
    (late_days <? 9 = false) ->
    (late_days <? 17 = true) ->
    (grade_comparison (Grade F Minus) g = Lt) ->
    (apply_late_policy late_days g) = (lower_grade g).
Proof.
  (* FILL IN HERE *) intros. unfold apply_late_policy. rewrite H. rewrite H0. reflexivity.
Qed.

End LateDays.

Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).

Fixpoint incr (m:bin) : bin :=
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
  match m with
  | Z => B1 Z
  | B0 n => B1 n
  | B1 n => B0 (incr n)
  end.

Fixpoint bin_to_nat (m:bin) : nat :=
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
  match m with
  | Z => O 
  | B0 n => (2 * (bin_to_nat n))
  | B1 n => (1 + (2 * (bin_to_nat n)))
end.

Example test_bin_incr1 : (incr (B1 Z)) = B0 (B1 Z).
(* FILL IN HERE *) Proof. simpl. reflexivity. Qed.
Example test_bin_incr2 : (incr (B0 (B1 Z))) = B1 (B1 Z).
(* FILL IN HERE *) Proof. simpl. reflexivity. Qed.
Example test_bin_incr3 : (incr (B1 (B1 Z))) = B0 (B0 (B1 Z)).
(* FILL IN HERE *) Proof. simpl. reflexivity. Qed.
Example test_bin_incr4 : bin_to_nat (B0 (B1 Z)) = 2.
(* FILL IN HERE *) Proof. simpl. reflexivity. Qed.
Example test_bin_incr5 :
        bin_to_nat (incr (B1 Z)) = 1 + bin_to_nat (B1 Z).
(* FILL IN HERE *) Proof. simpl. reflexivity. Qed.
Example test_bin_incr6 :
        bin_to_nat (incr (incr (B1 Z))) = 2 + bin_to_nat (B1 Z).
(* FILL IN HERE *) Proof. simpl. reflexivity. Qed.

(* Chapter 2 : Induction *)

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

Theorem add_assoc2 : forall n m p : nat,
  n + (m + p) = n + m + p.
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

Theorem eqb_refle : forall n : nat, (eqb n n) = true.
Proof.
  intros.
  induction n as [|n' IHn']. simpl. reflexivity.
  simpl. rewrite IHn'. reflexivity.
Qed.

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
  rewrite add_comm.
  assert (H: p + n = n + p).
  { rewrite add_comm. reflexivity. }
  rewrite <- H.
  rewrite add_assoc.
  reflexivity.
Qed.

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros n.
  induction n as [|n'].
    simpl.
    reflexivity.
    simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem mul_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros m n.
  induction m as [| m' IHm'].
  - rewrite mul_0_r.
    reflexivity.
  - simpl.
    rewrite -> IHm'.
    assert (H: forall a b : nat, a * (1 + b) = a + a * b).
    {
      intros a b.
      induction a as [| a' IHa'].
      - reflexivity.
      - Compute mult_n_Sm.
        (*      = mult_n_Sm
     : forall n m : nat, n * m + n = n * S m *)
        rewrite <- mult_n_Sm.
        Compute add_comm.
(*        = add_comm
     : forall n m : nat, n + m = m + n       *)
        rewrite -> add_comm.
        reflexivity.
    }
    rewrite -> H.
    reflexivity.
Qed.

Check leb.

Theorem plus_leb_compat_l : forall n m p : nat,
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
  induction p as [|p' IHp'].
  simpl.
  - intro. rewrite H. reflexivity.
  - intro. simpl. rewrite IHp'. reflexivity.  rewrite H. reflexivity.
Qed.

(* For each of the following theorems, first think about whether (a) it can be proved using only simplification and rewriting, (b) it also requires case analysis (destruct), or (c) it also requires induction. Write down your prediction. Then fill in the proof.
*)
Theorem leb_refl : forall n:nat,
  (n <=? n) = true.
  (* my guess: a / my proof: c *)
Proof.
  (* FILL IN HERE *)
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem zero_neqb_S : forall n:nat,
  0 =? (S n) = false.
    (* b / a *)
Proof.
  (* FILL IN HERE *)
  reflexivity.
Qed.
  
Theorem andb_false_r : forall b : bool,
  andb b false = false.
    (* b / b *)
Proof.
  (* FILL IN HERE *)
  intro b.
  destruct b.
  reflexivity.
  reflexivity.
Qed.

Theorem S_neqb_0 : forall n:nat,
  (S n) =? 0 = false.
    (* c / a *)
Proof.
  (* FILL IN HERE *)
  intros.
  reflexivity.
Qed.

Theorem mult_1_l : forall n:nat, 1 * n = n.
  (* c / c *)
Proof.
  (* FILL IN HERE *)
  intros.
  simpl.
  induction n as [|n' IHn'].
  reflexivity.
  simpl.
  rewrite IHn'.
  reflexivity.
Qed.

Theorem all3_spec : forall b c : bool,
  orb
    (andb b c)
    (orb (negb b)
         (negb c))
  = true.
    (* b / b*)
Proof.
  (* FILL IN HERE *)
  intros.
  destruct b.
  simpl. destruct c. reflexivity. reflexivity. reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
    (* c *)
Proof.
  (* FILL IN HERE *)
  induction n as [|n' IHn'].
  intros.
  simpl. reflexivity.
  intros. simpl.
  rewrite IHn'.
  rewrite add_assoc. reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
    (* c *)
Proof.
  (* FILL IN HERE *)
  induction n as [|n' IHn'].
  intros.
  simpl. reflexivity.
  intros. simpl.
  rewrite mult_plus_distr_r.
  rewrite IHn'. reflexivity.
Qed.

Theorem add_shuffle3' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  (* FILL IN HERE *)
  intros.
  rewrite add_assoc.
  replace (n + m) with (m + n).
  rewrite add_assoc. reflexivity.
  rewrite add_comm. reflexivity.
Qed.

