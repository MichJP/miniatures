Require Import List.
Require Import Nat.
Require Import Bool.

Import ListNotations.

Inductive Pebble : Type := Red | Green.

(* Define Pebble_beq and Pebble_eq_dec
 *   Pebble_beq : Pebble -> Pebble -> bool
 *   Pebble_eq_dec : forall x y : Pebble, {x = y} + {x <> y}
 *)
Scheme Equality for Pebble.

Definition flipColor (pebble : Pebble) : Pebble :=
  match pebble with
  | Red => Green
  | Green => Red
  end.

Fixpoint next (hd : Pebble) (jar : list Pebble) : Pebble :=
  match jar with
  | [] => hd
  | Red :: rest => next hd rest
  | Green :: rest => next (flipColor hd) rest
  end.

Definition run1 (jar : list Pebble) : Pebble :=
  match jar with
  | [] => Red
  | hd :: tl => next hd tl
  end.

Definition run2 (jar : list Pebble) : Pebble :=
  if (even (count_occ Pebble_eq_dec jar Green)) then Red else Green.

Lemma flipColor_involutive : forall a : Pebble, flipColor (flipColor a) = a.
Proof.
  destruct a;
  reflexivity.
Qed.

Lemma next_res : forall (a : Pebble) (jar : list Pebble), next a jar = Red \/ next a jar = Green.
Proof.
  intros.
  destruct (next a jar).
  - left.
    reflexivity.
  - right.
    reflexivity.
Qed.

Lemma run1_res : forall (jar : list Pebble), run1 jar = Red \/ run1 jar = Green.
Proof.
  destruct jar.
  - left.
    reflexivity.
  - apply next_res.
Qed.

Lemma next_inj1 : forall (jar : list Pebble), next Red jar = Red -> next Green jar = Green.
Proof.
  induction jar;
  try reflexivity.
  intros.
  destruct a.
  - simpl.
    simpl in H.
    apply IHjar, H.
  - simpl.
    simpl in H.
    destruct (next_res Red jar).
    + apply IHjar in H0.
      rewrite H in H0.
      inversion H0.
    + apply H0.
Qed.

Lemma next_inj2 : forall (jar : list Pebble), next Green jar = Green -> next Red jar = Red.
Proof.
  induction jar;
  try reflexivity.
  intros.
  destruct a.
  - simpl.
    simpl in H.
    apply IHjar.
    apply H.
  - simpl.
    simpl in H.
    destruct (next_res Green jar).
    + apply H0.
    + apply IHjar in H0.
      rewrite H in H0.
      inversion H0.
Qed.

Lemma flipColor_comm_part1 : forall jar : list Pebble, next Green jar = Red -> next Red jar = Green.
Proof.
  induction jar.
  - simpl.
    intro.
    symmetry.
    apply H.
  - destruct a.
    + simpl.
      apply IHjar.
    + simpl.
      apply next_inj1.
Qed.

Lemma flipColor_comm_part2 : forall jar : list Pebble, next Red jar = Green -> next Green jar = Red.
Proof.
  induction jar.
  - simpl.
    intro.
    symmetry.
    apply H.
  - destruct a.
    + simpl.
      apply IHjar.
    + simpl.
      apply next_inj2.
Qed.

Lemma bool_modus_tollens : forall (a b c d : bool), (a = c -> b = d) -> b = negb d -> a = negb c.
Proof.
  intros a b c d H H0.
  destruct a, b, c, d;
  try reflexivity;
  try apply H0;
  try inversion H0;
  try (apply H; reflexivity);
  symmetry;
  apply H;
  reflexivity.
Qed.

Lemma not_even_succ_even : forall (n : nat), even n = false -> even (S n) = true.
Proof.
  induction n as [ | n' IHn'].
  - intro H.
    inversion H.
  - intro H.
    simpl.
    apply (bool_modus_tollens (even n') (even (S n')) false true).
    + intro H0.
      apply IHn', H0.
    + apply H.
Qed.

Lemma even_succ : forall (n : nat), even n = true -> even (S n) = false.
Proof.
  induction n as [ | n' IHn'];
  try reflexivity.
  intros.
  simpl.
  apply (bool_modus_tollens (even n') (even (S n')) true false).
  - intro H0.
    apply IHn', H0.
  - apply H.
Qed.

Lemma lemma1 : forall (jar : list Pebble), run1 jar = Red -> next Green jar = Green.
Proof.
  induction jar.
  - reflexivity.
  - intros.
    destruct a.
    + simpl.
      simpl in H.
      apply next_inj1, H.
    + simpl.
      simpl in H.
      apply flipColor_comm_part1, H.
Qed.

Lemma lemma2 : forall (jar : list Pebble), run1 jar = Green -> next Green jar = Red.
Proof.
  induction jar.
  - intro.
    inversion H.
  - destruct a.
    + simpl.
      intro.
      apply flipColor_comm_part2, H.
    + simpl.
      apply next_inj2.
Qed.

Theorem th1 : forall jar : list Pebble, run1 jar = run2 jar.
Proof.
  unfold run2.
  induction jar as [ | hd tl IHjar];
  try reflexivity.
  destruct hd.
  - simpl.
    rewrite <- IHjar.
    unfold run1.
    induction tl as [ | hd' tl' _];
    try reflexivity.
    destruct hd';
    try reflexivity.
  - simpl (count_occ _ _ _).
    simpl (run1 _).
    destruct (run1_res tl) as [H | H];
    destruct (even (count_occ Pebble_eq_dec tl Green)) eqn:H1;
    rewrite H in IHjar;
    try inversion IHjar.
    + apply even_succ in H1.
      rewrite H1.
      apply lemma1, H.
    + apply not_even_succ_even in H1.
      rewrite H1.
      apply lemma2, H.
Qed.
