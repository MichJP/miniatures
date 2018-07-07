Require Import List.
Require Import Nat.
Require Import Bool.

Import ListNotations.

Inductive Pebble : Type := Red | Green.

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

Definition Pebble_eq_Green_bool (a : Pebble) : bool := if Pebble_eq_dec Green a then true else false.

Lemma next_res : forall (a : Pebble) (jar : list Pebble), next a jar = Red \/ next a jar = Green.
Proof.
  intros.
  destruct (next a jar).
  - left.
    reflexivity.
  - right.
    reflexivity.
Qed.

Lemma next_inj1 : forall (jar : list Pebble), next Red jar = Red -> next Green jar = Green.
Proof.
  induction jar; try reflexivity.
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
  induction jar; try reflexivity.
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

Lemma run1_res : forall (jar : list Pebble), run1 jar = Red \/ run1 jar = Green.
Proof.
  destruct jar.
  - left.
    reflexivity.
  - apply next_res.
Qed.

Lemma negb_true_false : negb true = false.
Proof.
  reflexivity.
Qed.

Lemma negb_false_true : negb false = true.
Proof.
  reflexivity.
Qed.

Lemma negb_cancel : forall (a b : bool), negb a = negb b -> a = b.
Proof.
  destruct a; destruct b.
  - reflexivity.
  - simpl.
    intro.
    inversion H.
  - simpl.
    intro.
    inversion H.
  - intro.
    reflexivity.
Qed.

Lemma not_odd_even : forall (n : nat), odd n = false -> even n = true.
Proof.
  intros.
  unfold odd in H.
  rewrite <- (negb_true_false) in H.
  apply negb_cancel in H.
  apply H.
Qed.

Lemma odd_not_even : forall (n : nat), odd n = true -> even n = false.
Proof.
  intros.
  unfold odd in H.
  rewrite <- negb_false_true in H.
  apply negb_cancel in H.
  apply H.
Qed.

Lemma bool_modus_tollens : forall (a b : bool), (a = true -> b = true) -> b = false -> a = false.
Proof.
  intros.
  destruct a; destruct b.
  - apply H0.
  - symmetry.
    apply H.
    reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma not_even_succ_even : forall (n : nat), even n = false -> even (S n) = true.
Proof.
  induction n.
  - intro.
    inversion H.
  - intro.
    simpl.
    apply not_odd_even.
    apply (bool_modus_tollens (odd n) (even (S n))).
    + intro.
      apply odd_not_even in H0.
      apply IHn in H0.
      rewrite H in H0.
      inversion H0.
    + apply H.
Qed.

Lemma even_succ_odd : forall (n : nat), even n = true -> odd (S n) = true.
Proof.
  induction n.
  - intros.
    unfold odd.
    reflexivity.
  - intro.
    unfold odd.
    simpl.
    symmetry.
    apply negb_sym.
    simpl.
    apply (bool_modus_tollens (even n) (odd (S n))).
    + intro.
      apply IHn in H0.
      unfold odd in H0.
      rewrite H in H0.
      inversion H0.
    + unfold odd.
      rewrite H.
      reflexivity.
Qed.

Lemma succ_even : forall (n : nat), even (S n) = true -> even n = false.
Proof.
  induction n.
  - intros.
    simpl in H.
    inversion H.
  - intro.
    simpl in H.
    apply odd_not_even.
    apply even_succ_odd.
    apply H.
Qed.

Lemma even_succ : forall (n : nat), even n = true -> even (S n) = false.
Proof.
  induction n.
  - reflexivity.
  - intros.
    simpl.
    apply succ_even.
    apply H.
Qed.

Lemma lemma2 : forall (jar : list Pebble), run1 jar = Red -> next Green jar = Green.
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

Lemma lemma3 : forall (jar : list Pebble), run1 jar = Green -> next Green jar = Red.
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
  intro.
  induction jar.
  - reflexivity.
  - destruct a.
    + simpl.
      unfold run2.
      simpl.
      unfold run2 in IHjar.
      rewrite <- IHjar.
      unfold run1.
      induction jar; try reflexivity.
      destruct a; try reflexivity.
    + unfold run2.
      simpl (count_occ _ _ _).
      simpl (run1 _).
      unfold run2 in IHjar.
      destruct (run1_res jar).
      * rewrite H in IHjar.
        destruct (even (count_occ Pebble_eq_dec jar Green)) eqn:H1.
        { apply even_succ in H1.
          rewrite H1.
          apply lemma2, H.
        }
        { inversion IHjar.
        }
      * rewrite H in IHjar.
        destruct (even (count_occ Pebble_eq_dec jar Green)) eqn:H1.
        { inversion IHjar.
        }
        { apply not_even_succ_even in H1.
          rewrite H1.
          apply lemma3, H.
        }
Qed.
