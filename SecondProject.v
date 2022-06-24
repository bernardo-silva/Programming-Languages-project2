(* Programming Languages: Project 2
 * 
 * You are required to complete the seven exercises below. 
 *
 * Important:
 *  - Do not change any existing code nor the type of any function 
 *    or theorem, otherwise you might not get any points. 
 *  - Do not delete any comments, except those marked as (*TODO*)
 *  - You can add new code or new lemmas (but make sure there's a good 
 *    reason for doing so)
 *
 * All you have to do is to solve the exercises that are clearly
 * marked as so. You have to replace the comments (*TODO*) by your 
 * own solution.
 *
 * We assume that you will follow the established code of ethics and 
 * submit your own work. Any student might be asked to present and 
 * explain their submission.
 *
 * This component is worth 20 points. Each question
 * shows how many points it is worth.
 *
 * Deadline: 24th June 2022, 23:59
 *)


(* We import the files from the book Software Foundations (vol. 2). 
   To make it easier, you might want to copy this file to the same 
   directory as the book. If you have problems importing the files
   below, get in touch with the teaching team. *)

Set Warnings "-notation-overridden,-parsing".

From SecondProject Require Import Maps.
From Coq Require Import Arith.PeanoNat. Import Nat.
From SecondProject Require Import Imp.
From SecondProject Require Import Hoare.
From SecondProject Require Import Smallstep.

Module SecondProject.

(* In this Coq Assessment, we will extend IMP with four new commands:

  - The first two are [assert] and [assume]. Both commands are ways
    to indicate that a certain statement should hold any time this part
    of the program is reached. However they differ as follows:

     - If an [assert] statement fails, it causes the program to go into
       an error state and exit.

     - If an [assume] statement fails, the program fails to evaluate
       at all. In other words, the program gets stuck and has no
       final state.

  - The [havoc] command, which is similar to the nondeterministic [any] 
    expression from the the [Imp] chapter. [havoc x] will set the
    value of variable x to a non-deterministic value.

  - Non-deterministic choice [c1 !! c2]. This chooses non-deterministically
    between [c1] and [c2]. For example, if we have [(X := 1) !! (X := 2)],
    only one of the assignments will be executed: on termination, [X] will
    either have value 1 or value 2 (only one of the assignments execute!)
*)



(* ################################################################# *)
(* EXERCISE 1 (1 point): Extend the syntax of IMP                    *)
(* ################################################################# *)


Inductive com : Type :=
  | CSkip
  | CAsgn (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com)
  | CAssert (b : bexp)
  | CAssume (b : bexp) 
  | CHavoc (x : string)
  | CNonDetChoice (c1 c2 : com).

Notation "'skip'"  :=
         CSkip (in custom com at level 0) : com_scope.
Notation "x := y"  :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99) : com_scope.

(** We can use the new notation defined here: *)
Notation "'assert' l" := (CAssert l)
                           (in custom com at level 8, l custom com at level 0).
Notation "'assume' l" := (CAssume l)
                          (in custom com at level 8, l custom com at level 0).
Notation "'havoc' l" := (CHavoc l)
                          (in custom com at level 60, l constr at level 0).

Notation "c1 !! c2" :=
  (CNonDetChoice c1 c2)
    (in custom com at level 90, right associativity) : com_scope.

(** To define the behavior of [assert] and [assume], we need to add
    notation for an error, which indicates that an assertion has
    failed. We modify the [ceval] relation, therefore, so that
    it relates a start state to either an end state or to [error].
    The [result] type indicates the end value of a program,
    either a state or an error: *)

Inductive result : Type :=
  | RNormal : state -> result
  | RError : result.


(* ################################################################### *)
(* EXERCISE 2 (1.5 points): Define a relational evaluation (big-step   *)
(*                          semantics). Some rules are given. Note the *)
(*                          use of RNormal / RError.                   *)
(* ################################################################### *)


Reserved Notation
         "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).

Inductive ceval : com -> state -> result -> Prop :=
  (* Old rules, several modified *)
  | E_Skip : forall st,
      st =[ skip ]=> RNormal st
  | E_Asgn  : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x := a1 ]=> RNormal (x !-> n ; st)
  | E_SeqNormal : forall c1 c2 st st' r,
      st  =[ c1 ]=> RNormal st' ->
      st' =[ c2 ]=> r ->
      st  =[ c1 ; c2 ]=> r
  | E_SeqError : forall c1 c2 st,
      st =[ c1 ]=> RError ->
      st =[ c1 ; c2 ]=> RError
  | E_IfTrue : forall st r b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> r ->
      st =[ if b then c1 else c2 end ]=> r
  | E_IfFalse : forall st r b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> r ->
      st =[ if b then c1 else c2 end ]=> r
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> RNormal st
  | E_WhileTrueNormal : forall st st' r b c,
      beval st b = true ->
      st  =[ c ]=> RNormal st' ->
      st' =[ while b do c end ]=> r ->
      st  =[ while b do c end ]=> r
  | E_WhileTrueError : forall st b c,
      beval st b = true ->
      st =[ c ]=> RError ->
      st =[ while b do c end ]=> RError
  | E_AssertTrue : forall st b,
      beval st b = true ->
      st =[ assert b ]=> RNormal st
  | E_AssertFalse : forall st b,
      beval st b = false ->
      st =[ assert b ]=> RError
  | E_Assume : forall st b,
      beval st b = true ->
      st =[ assume b ]=> RNormal st
  | E_Havoc : forall st X n,
    st =[ havoc X ]=> RNormal (X !-> n ; st)
  | E_NonDetChoice1: forall st st' c1 c2,
    st =[ c1 ]=> RNormal st' ->
    st =[ c1 !! c2 ]=> RNormal st'
  | E_NonDetChoice2: forall st st' c1 c2,
    st =[ c2 ]=> RNormal st' ->
    st =[ c1 !! c2 ]=> RNormal st'
where "st '=[' c ']=>' r" := (ceval c st r).


(** We redefine hoare triples: Now, [{{P}} c {{Q}}] means that,
    whenever [c] is started in a state satisfying [P], and terminates
    with result [r], then [r] is not an error and the state of [r]
    satisfies [Q]. *)

Definition hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st r,
     st =[ c ]=> r  -> P st  ->
     (exists st', r = RNormal st' /\ Q st').


Notation "{{ P }}  c  {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c custom com at level 99)
  : hoare_spec_scope.

(* ################################################################## *)
(* EXERCISE 3 (3.5 points): Prove properties involving [assert] and   *)
(*            [assume]. To test your understanding of the new         *)
(*            operators, prove [assume_false], [assert_assume_differ] *)
(*            and [assert_implies_assume].                            *)
(*            For the first, show that any triple where we assume     *)
(*            a false condition is always valid.                      *)
(*            For the second, give an example precondition and        *)
(*            postcondition that are satisfied by the [assume]        *)
(*            statement but not by the [assert] statement.  For the   *)
(*            third, prove that any triple for [assert] also works    *)
(*            for [assume].                                           *)
(* ################################################################## *)

Theorem assume_false: forall P Q b,
       (forall st, beval st b = false) ->
       ({{P}} assume b {{Q}}).
Proof.
  intros P Q b H st r Himp Hhoare.
  inversion Himp; subst.
  rewrite H in H1.
  discriminate.
Qed.

Theorem assert_assume_differ : exists P b Q,
       ({{P}} assume b {{Q}})
  /\ ~ ({{P}} assert b {{Q}}).
Proof.
  exists True.
  exists BFalse.
  exists False.
  split.
  - apply assume_false. 
    reflexivity.
  - intros H.
    unfold hoare_triple in H. 
    specialize (H empty_st RError).
    destruct H.
    -- apply E_AssertFalse. reflexivity.
    -- reflexivity.
    -- destruct H. discriminate.
Qed.

Theorem assert_implies_assume : forall P b Q,
     ({{P}} assert b {{Q}})
  -> ({{P}} assume b {{Q}}).
Proof.
  unfold hoare_triple.
  intros.
  inversion H0; subst.
  specialize (H st (RNormal st)).
  destruct H.
  - apply E_AssertTrue. assumption.
  - assumption.
  - destruct H.
    exists x.
    split; assumption.
Qed.

(* ################################################################# *)
(* EXERCISE 4 (5 points): Define Hoare rules for the new operators   *)
(*                        in IMP. See sub-exercises below.           *)
(* ################################################################# *)

(** For your benefit, we provide proofs for the old hoare rules
    adapted to the new semantics. *)

Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} X := a {{Q}}.
Proof.
  unfold hoare_triple.
  intros Q X a st st' HE HQ.
  inversion HE. subst.
  eexists. split; try reflexivity. assumption.
Qed.

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  unfold hoare_triple, "->>".
  intros P P' Q c Hhoare Himp st st' Heval Hpre.
  apply Hhoare with (st := st).
  - assumption.
  - apply Himp. assumption.
Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P Q Q' c Hhoare Himp.
  intros st r Hc HP.
  unfold hoare_triple in Hhoare.
  assert (exists st', r = RNormal st' /\ Q' st').
  { apply (Hhoare st); assumption. }
  destruct H as [st' [Hr HQ']].
  exists st'. split; try assumption.
  apply Himp. assumption.
Qed.

Theorem hoare_seq : forall P Q R c1 c2,
  {{Q}} c2 {{R}} ->
  {{P}} c1 {{Q}} ->
  {{P}} c1;c2 {{R}}.
Proof.
  intros P Q R c1 c2 H1 H2 st r H12 Pre.
  inversion H12; subst.
  - eapply H1.
    + apply H6.
    + apply H2 in H3. apply H3 in Pre.
        destruct Pre as [st'0 [Heq HQ]].
        inversion Heq; subst. assumption.
  - (* Find contradictory assumption *)
     apply H2 in H5. apply H5 in Pre.
     destruct Pre as [st' [C _]].
     inversion C.
Qed.

Theorem hoare_skip : forall P,
     {{P}} skip {{P}}.
Proof.
  intros P st st' H HP. inversion H. subst.
  eexists. split. reflexivity. assumption.
Qed.

Theorem hoare_if : forall P Q (b:bexp) c1 c2,
  {{ P /\ b }} c1 {{Q}} ->
  {{ P /\ ~ b}} c2 {{Q}} ->
  {{P}} if b then c1 else c2 end {{Q}}.
(** That is (unwrapping the notations):

      Theorem hoare_if : forall P Q b c1 c2,
        {{fun st => P st /\ bassn b st}} c1 {{Q}} ->
        {{fun st => P st /\ ~ (bassn b st)}} c2 {{Q}} ->
        {{P}} if b then c1 else c2 end {{Q}}.
*)
Proof.
  intros P Q b c1 c2 HTrue HFalse st st' HE HP.
  inversion HE; subst; eauto.
Qed.


Theorem hoare_while : forall P (b:bexp) c,
  {{P /\ b}} c {{P}} ->
  {{P}} while b do c end {{P /\ ~ b}}.
Proof.
  intros P b c Hhoare st st' He HP.
  remember (<{while b do c end}>) as wcom eqn:Heqwcom.
  induction He;
    try (inversion Heqwcom); subst; clear Heqwcom.
  - (* E_WhileFalse *)
    eexists. split. reflexivity. split.
    assumption. apply bexp_eval_false. assumption.
  - (* E_WhileTrueNormal *)
    clear IHHe1.
    apply IHHe2. reflexivity.
    clear IHHe2 He2 r.
    unfold hoare_triple in Hhoare.
    apply Hhoare in He1.
    + destruct He1 as [st1 [Heq Hst1]].
        inversion Heq; subst.
        assumption.
    + split; assumption.
  - (* E_WhileTrueError *)
     exfalso. clear IHHe.
     unfold hoare_triple in Hhoare.
     apply Hhoare in He.
     + destruct He as [st' [C _]]. inversion C.
     + split; assumption.
Qed.

(** (End of proofs given.) *)

(* ================================================================= *)
(* EXERCISE 4.1: State and prove [hoare_assert]                      *)
(* ================================================================= *)

Theorem hoare_assert: forall P (b: bexp),
  {{P /\ b}} assert b {{P /\ b}}.
Proof.
  intros P b st r H Hpre.
  inversion H; subst.
  - exists st. 
    split. reflexivity. assumption.
  - destruct Hpre. inversion H2. rewrite H1 in H4. discriminate. 
Qed.

(* ================================================================= *)
(* EXERCISE 4.2: State and prove [hoare_assume]                      *)
(* ================================================================= *)

Theorem hoare_assume: forall (P:Assertion) (b:bexp),
  {{P \/ ~b }} assume b {{P}}.
  (*TODO: Hoare proof rule for [assume b] *)
Proof.
  intros P b st r Heval Hpre.
  inversion Heval; subst.
  exists st. split.
  - reflexivity.
  - inversion Hpre.
    -- assumption.
    -- unfold not in H. contradiction.
  (* TODO *)
Qed.


(* ================================================================= *)
(* EXERCISE 4.3: State and prove [hoare_havoc]. Define [havoc_pre]   *)
(*               and use it in the definition of [hoare_havoc].      *)
(* ================================================================= *)

Definition havoc_pre (X : string) (Q : Assertion) : Assertion :=
  fun st => forall n, st X = n /\ Q st.

Theorem hoare_havoc : forall (Q : Assertion) (X : string),
  {{ havoc_pre X Q }} havoc X {{ Q }}.
Proof.
  intros Q X st r Heval Hpre.
  inversion Heval; subst.
  unfold havoc_pre in Hpre.
  specialize (Hpre n).
  inversion Hpre; subst.
  eexists. split.
  - reflexivity.
  - rewrite t_update_same. assumption.
  (* TODO *)
Qed.


(* ================================================================= *)
(* EXERCISE 4.4: State and prove [hoare_choice]                      *)
(* ================================================================= *)

Theorem hoare_choice : forall P1 c1 Q1 P2 c2 Q2,
  {{P1}} c1 {{Q1}} ->
  {{P2}} c2 {{Q2}} ->
  {{P1 /\ P2}} c1 !! c2 {{Q1 \/ Q2}}.
  (*TODO: Hoare proof rule for [c1 !! c2] *)
Proof.
  intros P1 c1 Q1 P2 c2 Q2 Hc1 Hc2 st r Heval Hpre.
  destruct Hpre as [HP1 HP2].
  inversion Heval; subst.
  - eexists. split.
    -- reflexivity.
    -- specialize (Hc1 st (RNormal st')).
       destruct Hc1; try assumption.
       destruct H. inversion H; subst.
       left. assumption.
  - eexists. split.
    -- reflexivity.
    -- specialize (Hc2 st (RNormal st')).
       destruct Hc2; try assumption.
       destruct H. inversion H; subst.
       right. assumption.
  (* TODO *)
Qed.


(* ================================================================= *)
(* EXERCISE 4.5: Use the proof rules defined to prove the following  *)
(*               example.                                            *)
(* ================================================================= *)

Example assert_assume_example:
  {{ X = 1 }}
  assume (X = 2);
  X := X + 1
  {{ X = 42 }}.  
Proof.
intros st r Heval Hpre.
inversion Heval; subst.
  - inversion H1; subst.
    unfold beval in H3.
    simpl in *.
    rewrite Hpre in H3.
    discriminate.
  - inversion H3; subst.
Qed.


(* ################################################################### *)
(* EXERCISE 5 (2.5 points): Define a relational evaluation (small-step *)
(*                          semantics). Some rules are given.          *)
(* ################################################################### *)

Reserved Notation " t '/' st '-->' t' '/' st' "
                  (at level 40, st at level 39, t' at level 39).


Inductive cstep : (com * result)  -> (com * result) -> Prop :=
  (* Old part *)
  | CS_AsgnStep : forall st i a a',
      a / st -->a a' ->
      <{ i := a }> / RNormal st --> <{ i := a' }> / RNormal st
  | CS_Asgn : forall st i n,
      <{ i := (ANum n) }> / RNormal st --> <{ skip }> / RNormal (i !-> n ; st)
  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 / st --> c1' / st' ->
      <{ c1 ; c2 }> / st --> <{ c1' ; c2 }> / st'
  | CS_SeqFinish : forall st c2,
      <{ skip ; c2 }> / st --> c2 / st
  | CS_IfStep : forall st b b' c1 c2,
      b / st -->b b' ->
      <{if b then c1 else c2 end }> / RNormal st 
      --> <{ if b' then c1 else c2 end }> / RNormal st
  | CS_IfTrue : forall st c1 c2,
      <{ if true then c1 else c2 end }> / st --> c1 / st
  | CS_IfFalse : forall st c1 c2,
      <{ if false then c1 else c2 end }> / st --> c2 / st
  | CS_While : forall st b c1,
          <{while b do c1 end}> / st 
      --> <{ if b then (c1; while b do c1 end) else skip end }> / st
  | CS_AssertStep: forall st b b',
    b / st -->b b' ->
    <{ assert b }> / RNormal st --> <{ assert b' }> / RNormal st
  | CS_AssertTrue: forall st,
    <{ assert true }> / RNormal st --> <{ skip }> / RNormal st
  | CS_AssertFalse: forall st,
    <{ assert false }> / RNormal st --> <{ skip }> / RError
  | CS_AssumeStep: forall st b b',
    b / st -->b b' ->
    <{ assume b }> / RNormal st --> <{ assume b' }> / RNormal st
  | CS_AssumeTrue: forall st,
    <{ assume true }> / RNormal st --> <{ skip }> / RNormal st
  | CS_Havoc : forall st i n,
      <{ havoc i }> / RNormal st --> <{ skip }> / RNormal (i !-> n ; st)
  | CS_Choice1 : forall st c1 c2,
      <{ c1 !! c2 }> / st --> c1 / st
  | CS_Choice2 : forall st c1 c2,
      <{ c1 !! c2 }> / st --> c2 / st 
  (*TODO: rule(s) for Assert *)
  (*TODO: rule(s) for Assume *)
  (*TODO: rule(s) for Havoc *)
  (*TODO: rule(s) for Choice *)

  where " t '/' st '-->' t' '/' st' " := (cstep (t,st) (t',st')).

Definition cmultistep := multi cstep.

Notation " t '/' st '-->*' t' '/' st' " :=
   (multi cstep  (t,st) (t',st'))
   (at level 40, st at level 39, t' at level 39).


(* ################################################################# *)
(* EXERCISE 6 (2.5 points): Show that the program [prog1] can        *)
(*            successfully terminate in a state where [X=2] and it   *)
(*            can also terminate in an error state. Use the rules    *)
(*            defined in [cstep]. You can use [multi_step] and       *)
(*            [multi_refl].                                          *) 
(* ################################################################# *)



(* We start with an example of a proof about a simple program that uses
the rules already provided. *)

Definition prog0 : com :=
  <{ X := X + 1 ; X := X + 2 }>.

Example prog0_example:
  exists st',
       prog0 / RNormal (X !-> 1) -->* <{ skip }> / RNormal st'
    /\ st' X = 4.
Proof.
  eexists. split.
  unfold prog0.

  (* Sequence and X := X+1*)
  eapply multi_step. apply CS_SeqStep. 
  apply CS_AsgnStep. apply AS_Plus1. apply AS_Id.
  eapply multi_step. apply CS_SeqStep. apply CS_AsgnStep. apply AS_Plus.
  simpl. eapply multi_step. apply CS_SeqStep. apply CS_Asgn. eapply multi_step. 
  apply CS_SeqFinish.

  (* X := X + 2 *)
  eapply multi_step. apply CS_AsgnStep. apply AS_Plus1. apply AS_Id.
  eapply multi_step. apply CS_AsgnStep. apply AS_Plus.
  simpl. eapply multi_step. apply CS_Asgn. eapply multi_refl.

  reflexivity.
Qed. 


Definition prog1 : com :=
  <{ 
  assume (X = 1);
  ((X := X + 1) !! (X := 3));
  assert (X = 2)
  }>.

Example prog1_example1:
  exists st',
       prog1 / RNormal (X !-> 1) -->* <{ skip }> / RNormal st'
    /\ st' X = 2.
Proof.
  eexists. 
  split.
  unfold prog1.
  eapply multi_step.
  apply CS_SeqStep.
  apply CS_AssumeStep.
  apply BS_Eq1. 
  apply AS_Id.
  eapply multi_step.
  apply CS_SeqStep.
  apply CS_AssumeStep.
  apply BS_Eq.
  eapply multi_step.
  apply CS_SeqStep.
  apply CS_AssumeTrue.
  eapply multi_step.
  apply CS_SeqFinish.
  eapply multi_step.
  apply CS_SeqStep.
  apply CS_Choice1.
  eapply multi_step.
  apply CS_SeqStep.
  apply CS_AsgnStep.
  apply AS_Plus1.
  apply AS_Id.
  eapply multi_step.
  apply CS_SeqStep.
  apply CS_AsgnStep.
  apply AS_Plus.
  simpl.
  eapply multi_step.
  apply CS_SeqStep.
  apply CS_Asgn.
  eapply multi_step.
  apply CS_SeqFinish.
  eapply multi_step.
  apply CS_AssertStep.
  apply BS_Eq1. 
  apply AS_Id.
  eapply multi_step.
  apply CS_AssertStep.
  apply BS_Eq.
  eapply multi_step.
  apply CS_AssertTrue.
  eapply multi_refl.
  reflexivity.
Qed.

Example prog1_example2:
       prog1 / RNormal (X !-> 1) -->* <{ skip }> / RError.
Proof.
  unfold prog1.
  eapply multi_step.
  apply CS_SeqStep.
  apply CS_AssumeStep.
  apply BS_Eq1. apply AS_Id.
  eapply multi_step.
  apply CS_SeqStep.
  apply CS_AssumeStep.
  apply BS_Eq.
  eapply multi_step.
  apply CS_SeqStep.
  apply CS_AssumeTrue.
  eapply multi_step.
  apply CS_SeqFinish.
  eapply multi_step.
  apply CS_SeqStep.
  apply CS_Choice2.
  eapply multi_step.
  apply CS_SeqStep.
  apply CS_Asgn.
  eapply multi_step.
  apply CS_SeqFinish.
  eapply multi_step.
  apply CS_AssertStep.
  apply BS_Eq1.
  apply AS_Id.
  eapply multi_step.
  apply CS_AssertStep.
  apply BS_Eq.
  eapply multi_step.
  apply CS_AssertFalse.
  eapply multi_refl.
Qed.
    

(* ################################################################# *)
(* EXERCISE 7 (4 points): Prove the following properties.            *)
(* ################################################################# *)

Lemma one_step_aeval_a: forall st a a',
  a / st -->a a' ->
  aeval st a = aeval st a'.
Proof.
induction a; intros.
  - inversion H.
  - inversion H. reflexivity.
  - inversion H; subst; simpl; try reflexivity.
    + apply IHa1 in H3. 
      rewrite H3. reflexivity.
    + apply IHa2 in H4. 
      rewrite H4. reflexivity.
  - inversion H; subst; simpl; try reflexivity.
    + apply IHa1 in H3. 
      rewrite H3. reflexivity.
    + apply IHa2 in H4. 
      rewrite H4. reflexivity.
  - simpl. inversion H; subst; simpl; try reflexivity.
    + apply IHa1 in H3. 
      rewrite H3. reflexivity.
    + apply IHa2 in H4. 
      rewrite H4. reflexivity.
  (* TODO (Hint: you can prove this by induction on a) *)
Qed.

Lemma one_step_beval_b: forall st b b',
  b / st -->b b' ->
  beval st b = beval st b'.
Proof.
induction b; intros.
  - inversion H.
  - inversion H.
  - simpl. inversion H; subst; simpl.
    + apply one_step_aeval_a in H3. rewrite H3. reflexivity.
    + apply one_step_aeval_a in H4. rewrite H4. reflexivity.
    + destruct (n1 =? n2); simpl; reflexivity.
  - simpl. inversion H; subst; simpl.
    + apply one_step_aeval_a in H3. rewrite H3. reflexivity.
    + apply one_step_aeval_a in H4. rewrite H4. reflexivity.
    + destruct (n1 <=? n2); simpl; reflexivity.
  - simpl. inversion H; subst; simpl.
    + apply IHb in H1.  rewrite H1. reflexivity.
    + reflexivity.
    + reflexivity. 
  - simpl. inversion H; subst; simpl; try reflexivity.
    + apply IHb1 in H3.  rewrite H3. reflexivity.
    + apply IHb2 in H3.  rewrite H3. reflexivity.
Qed.  


Lemma aval_asgn_if: forall st x a result,
  aval a ->
  st =[ x := a ]=> result ->
  <{ x := a }> / RNormal st -->* <{ skip }> / result.
Proof.
intros st x a r Hval Heval.
inversion Heval; subst.
inversion Hval; subst. eapply multi_step.
  - apply CS_Asgn.
  - eapply multi_refl.
Qed.


Lemma small_step_big_step1: forall c c' st st' st'',
   c/RNormal st --> c'/RNormal st'
-> st' =[ c' ]=> RNormal st''
-> st =[ c ]=> RNormal st''.
Proof.
induction c; intros c' st st' st'' Hsmall Hbig.
  (* skip *)
  - inversion Hsmall.
  (* x := a *) 
  - inversion Hsmall; subst.
    + inversion Hbig; subst. 
      apply one_step_aeval_a in H0. destruct H0.
      apply E_Asgn. reflexivity.
    + inversion Hbig; subst.
      apply E_Asgn. reflexivity.
  (* c1; c2 *)
  - inversion Hsmall; subst.
    + inversion Hbig; subst.
      eapply IHc1 in H2; try eassumption.
      eapply E_SeqNormal; try eassumption.
    + eapply E_SeqNormal.
      eapply E_Skip. assumption.
  (* if *)
  - inversion Hsmall; subst.
    inversion Hbig; subst.
    + apply one_step_beval_b in H0.
      eapply E_IfTrue; try assumption.
      rewrite H0. assumption.
    + apply one_step_beval_b in H0.
      eapply E_IfFalse; try assumption.
      rewrite H0. assumption.
    + eapply E_IfTrue; try reflexivity; try assumption.
    + eapply E_IfFalse; try reflexivity; try assumption.
  (* while *)
  - inversion Hsmall; subst.
    inversion Hbig; subst.
    + inversion H5; subst. 
      eapply E_WhileTrueNormal in H6; try eassumption.
    + inversion H5; subst. apply E_WhileFalse. assumption.
  (* assert *)
  - inversion Hsmall; subst.
    + inversion Hbig; subst. apply E_AssertTrue.
      apply one_step_beval_b in H0. rewrite H0. assumption.
    + inversion Hbig; subst.
      apply E_AssertTrue. reflexivity.
  (* assume *)
  - inversion Hsmall; subst.
    + inversion Hbig; subst. apply E_Assume. 
      apply one_step_beval_b in H0. rewrite H0. assumption.
    + inversion Hbig; subst. apply E_Assume. reflexivity.
  (* havoc *)
  - inversion Hsmall; subst. inversion Hbig; subst.
    apply E_Havoc.
  (* c1 !! c2 *)
  - inversion Hsmall; subst.
    + apply E_NonDetChoice1. eassumption.
    + apply E_NonDetChoice2. assumption. 
  (* TODO (Hint: you can prove this by induction on c) *)
Qed. 


End SecondProject.


