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