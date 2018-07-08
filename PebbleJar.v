Require Import List.
Require Import Nat.
Require Import Bool.

Import ListNotations.

(* Lecture: Reasoning About Programs
 * Solving 2 problems using programing - Dijkstra, 1990
 * URL: https://youtu.be/GX3URhx6i2E
 *
 * Formalization of the first problem
 *)

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
  intros a jar.
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

Lemma next_inj : forall (jar : list Pebble) (a : Pebble), next a jar = a -> next (flipColor a) jar = flipColor a.
Proof.
  induction jar as [ | hd tl IHjar];
  try reflexivity.
  intros a H.
  destruct hd, (next_res a tl), a;
  try apply IHjar, H;
  try apply H0;
  apply IHjar in H0;
  simpl in H, H0;
  rewrite H in H0;
  inversion H0.
Qed.

Lemma flipColor_comm : forall (jar : list Pebble) (a : Pebble), next a jar = flipColor a -> next (flipColor a) jar = a.
Proof.
  induction jar as [ | hd tl IHjar].
  - symmetry.
    apply H.
  - destruct hd.
    + apply IHjar.
    + intros a H.
      rewrite <- flipColor_involutive.
      apply (next_inj tl (flipColor a)), H.
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
    apply (bool_modus_tollens (even n') (even (S n')) false true).
    + intro H0.
      apply IHn', H0.
    + apply H.
Qed.

Lemma even_succ : forall (n : nat), even n = true -> even (S n) = false.
Proof.
  induction n as [ | n' IHn'];
  try reflexivity.
  intro H.
  apply (bool_modus_tollens (even n') (even (S n')) true false).
  - intro H0.
    apply IHn', H0.
  - apply H.
Qed.

Lemma lemma1 : forall (jar : list Pebble), run1 jar = Red -> next Green jar = Green.
Proof.
  destruct jar as [ | hd tl];
  try reflexivity.
  intros H.
  destruct hd.
  - apply next_inj in H.
    apply H.
  - apply flipColor_comm in H.
    apply H.
Qed.

Lemma lemma2 : forall (jar : list Pebble), run1 jar = Green -> next Green jar = Red.
Proof.
  destruct jar as [ | hd tl];
  intro H.
  - inversion H.
  - destruct hd.
    + apply flipColor_comm in H.
      apply H.
    + apply next_inj in H.
      apply H.
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
