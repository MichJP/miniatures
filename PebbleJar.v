Require Import List.
Require Import Nat.
Require Import Lt.
Require Import Compare_dec.
Require Import Bool.

Import ListNotations.

Inductive Pebble : Type := Red | Green.

Scheme Equality for Pebble.

Definition flipColor (pebble : Pebble) : Pebble :=
  match pebble with
  | Red => Green
  | Green => Red
  end.

Fixpoint next (hd : Pebble) (jar : list Pebble) : list Pebble :=
  match jar with
  | [] => [hd]
  | Red :: rest => next hd rest
  | Green :: rest => next (flipColor hd) rest
  end.

Definition run1 (jar : list Pebble) : list Pebble :=
  match jar with
  | [] => [Red]
  | hd :: tl => next hd tl
  end.

Definition run2 (jar : list Pebble) : list Pebble :=
  if (even (count_occ Pebble_eq_dec jar Green)) then [Red] else [Green].

Lemma flipColor_involutive : forall a : Pebble, flipColor (flipColor a) = a.
Proof.
  destruct a;
  reflexivity.
Qed.

Lemma zero_less_than_one : 0 < 1.
Proof.
  assert (0 <> 1).
  - discriminate.
  - apply (neq_0_lt 1 H).
Qed.

Lemma singleton_has_elem : forall (l : list Pebble), length l = 1 -> exists (k : Pebble), In k l.
Proof.
  intros.
  generalize zero_less_than_one; intro.
  rewrite <- H in H0.
  generalize (@nth_In Pebble 0 l Red H0);
  intros.
  exists (@nth Pebble 0 l Red).
  apply H1.
Qed.

Lemma next_red_idem : forall (a : Pebble) (jar : list Pebble), next a (Red :: jar) = next a jar.
Proof.
  reflexivity.
Qed.

Lemma next_green_involutive : forall (a : Pebble) (jar : list Pebble), next a (Green :: Green :: jar) = next a jar.
Proof.
  intros.
  simpl.
  rewrite flipColor_involutive.
  reflexivity.
Qed.

Definition Pebble_eq_Green_bool (a : Pebble) : bool := if Pebble_eq_dec Green a then true else false.

Lemma next_red_idem_list : forall (a : Pebble) (jar : list Pebble), next a (filter Pebble_eq_Green_bool jar) = next a jar.
Proof.
  intros.
  generalize dependent a.
  induction jar.
  - reflexivity.
  - destruct a.
    + apply IHjar.
    + simpl.
      intro.
      apply IHjar.
Qed.

Lemma next_succ : forall (jar : list Pebble) (a : Pebble), next a jar = next (flipColor a) (Green :: jar).
Proof.
  induction jar.
  - destruct a.
    + reflexivity.
    + reflexivity.
  - destruct a0; destruct a; try reflexivity.
Qed.

Lemma next_idem : forall (jar : list Pebble) (a : Pebble), next a jar = next a (Red :: jar).
Proof.
  reflexivity.
Qed.

Lemma next_succ_succ : forall (jar : list Pebble) (a : Pebble), next a jar = next a (Green :: Green :: jar).
Proof.
  intros.
  generalize (next_succ (Green :: jar) (flipColor a)); intro.
  rewrite flipColor_involutive in H.
  rewrite <- H.
  apply next_succ.
Qed.

Lemma count_length : forall jar : list Pebble, count_occ Pebble_eq_dec jar Green = length (filter Pebble_eq_Green_bool jar).
Proof.
  induction jar.
  - reflexivity.
  - destruct a.
    + apply IHjar.
    + simpl.
      rewrite IHjar.
      reflexivity.
Qed.

Lemma next_length : forall (jar : list Pebble) (a : Pebble), length (next a jar) = 1.
Proof.
  induction jar.
  - reflexivity.
  - intro.
    simpl.
    destruct a.
    + apply (IHjar a0).
    + apply (IHjar (flipColor a0)).
Qed.

Lemma next_or : forall (jar : list Pebble) (a b : Pebble), In a (next b jar) \/ In (flipColor a) (next b jar).
Proof.
  induction jar.
  - intros.
    simpl.
    destruct a; destruct b.
    + left.
      left.
      reflexivity.
    + right.
      left.
      reflexivity.
    + right.
      left.
      reflexivity.
    + left.
      left.
      reflexivity.
  - intros.
    simpl.
    destruct a.
    + apply (IHjar a0 b).
    + apply (IHjar a0 (flipColor b)).
Qed.

Lemma singleton_property : forall {A : Type} (x : A) (l : list A), length l = 1 -> In x l -> l = [x].
Proof.
  intros.
  destruct l.
  - exfalso.
    apply (@in_nil A x H0).
  - inversion H.
    apply length_zero_iff_nil in H2.
    simpl in H0.
    destruct H0.
    + simpl in H.
      rewrite H0.
      rewrite H2.
      reflexivity.
    + exfalso.
      rewrite H2 in H0.
      apply (@in_nil A x H0).
Qed.

Lemma next_singleton : forall (a : Pebble) (jar : list Pebble), next a jar = [Red] \/ next a jar = [Green].
Proof.
  intros.
  generalize (next_length jar a); intro.
  generalize (next_or jar Red a); intro.
  simpl in H0.
  destruct H0.
  - left.
    apply singleton_property.
    + apply H.
    + apply H0.
  - right.
    apply singleton_property.
    + apply H.
    + apply H0.
Qed.

Lemma n_less_than_succ : forall (n : nat), n < S n.
Proof.
  induction n.
  - apply zero_less_than_one.
  - apply lt_n_S.
    apply IHn.
Qed.

Lemma list_range : forall (n : nat), exists (l : list nat), length l = n /\ forall (m : nat), m < n -> In m l.
Proof.
  induction n.
  - exists [].
    simpl.
    split.
    + reflexivity.
    + intros.
      induction m.
      * generalize (lt_irrefl 0); intro.
        apply (H0 H).
      * apply IHm.
        generalize (n_less_than_succ m); intro.
        apply (lt_trans m (S m) 0).
        { apply H0.
        }
        { apply H.
        }
  - destruct IHn.
    destruct H.
    exists (n :: x).
    split.
    + simpl.
      rewrite H.
      reflexivity.
    + intros.
      simpl.
      apply (lt_n_Sm_le m n) in H1.
      generalize (lt_eq_lt_dec m n); intro.
      destruct H2.
      * destruct s.
        { right.
          apply (H0 m l).
        }
        { left.
          symmetry.
          apply e.
        }
      * exfalso.
        apply (lt_not_le n m l H1).
Qed.

Lemma singleton_bin : forall (jar : list Pebble), length jar = 1 -> jar = [Red] \/ jar = [Green].
Proof.
  intros.
  generalize (singleton_has_elem jar H); intro.
  destruct H0.
  destruct x.
  simpl in H0.
  - left.
    apply (singleton_property Red jar H H0).
  - right.
    apply (singleton_property Green jar H H0).
Qed.

Lemma red_idem : forall (a : Pebble) (jar : list Pebble), next a (Red :: jar) = [a] -> next a jar = [a].
Proof.
  intros.
  rewrite <- H.
  reflexivity.
Qed.

Lemma next_inj1 : forall (jar : list Pebble), next Red jar = [Red] -> next Green jar = [Green].
Proof.
  induction jar.
  - intro.
    reflexivity.
  - intros.
    destruct a.
    + simpl.
      simpl in H.
      apply IHjar.
      apply H.
    + simpl.
      simpl in H.
      destruct (next_singleton Red jar).
      * apply IHjar in H0.
        rewrite H in H0.
        inversion H0.
      * apply H0.
Qed.

Lemma next_inj2 : forall (jar : list Pebble), next Green jar = [Green] -> next Red jar = [Red].
Proof.
  induction jar.
  - intro.
    reflexivity.
  - intros.
    destruct a.
    + simpl.
      simpl in H.
      apply IHjar.
      apply H.
    + simpl.
      simpl in H.
      destruct (next_singleton Green jar).
      * apply H0.
      * apply IHjar in H0.
        rewrite H in H0.
        inversion H0.
Qed.

Lemma flipColor_comm_part1 : forall jar : list Pebble, next Green jar = [Red] -> next Red jar = [Green].
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

Lemma flipColor_comm_part2 : forall jar : list Pebble, next Red jar = [Green] -> next Green jar = [Red].
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

Lemma flipColor_comm : forall (a : Pebble) (jar : list Pebble), next a jar = [a] -> next (flipColor a) jar = [flipColor a].
Proof.
  intros.
  generalize dependent a.
  induction jar.
  - reflexivity.
  - intros.
    simpl.
    destruct a.
    + apply IHjar.
      apply red_idem.
      apply H.
    + simpl in H.
      rewrite flipColor_involutive.
      destruct a0.
      * simpl.
        simpl in H.
        apply flipColor_comm_part1.
        apply H.
      * simpl.
        simpl in H.
        apply flipColor_comm_part2.
        apply H.
Qed.

Lemma res_flipColor : forall (a : Pebble) (jar : list Pebble), next (flipColor a) jar = [a] -> next a jar = [flipColor a].
Proof.
  intro a.
  induction jar.
  - intro.
    destruct a;
    inversion H.
  - generalize dependent a.
    simpl.
    destruct a0.
    + intros.
      apply IHjar.
      apply H.
    + intros.
      apply flipColor_comm.
      rewrite flipColor_involutive in H.
      apply H.
Qed.

Lemma flipColor_res : forall (a : Pebble) (jar : list Pebble), next a jar = [a] -> next (flipColor a) jar = [flipColor a].
Proof.
  intro a.
  induction jar.
  - destruct a;
    intro;
    reflexivity.
  - simpl.
    destruct a0.
    + intro.
      apply IHjar.
      apply H.
    + intros.
      rewrite flipColor_involutive.
      apply res_flipColor.
      apply H.
Qed.

Lemma next_res : forall (a : Pebble) (jar : list Pebble), next a jar = [Red] \/ next a jar = [Green].
Proof.
  intro a.
  induction jar.
  - destruct a.
    + left. reflexivity.
    + right. reflexivity.
  - destruct IHjar.
    + simpl.
      destruct a0.
      * left. apply H.
      * destruct a.
        { simpl.
          apply next_singleton.
        }
        { right.
          simpl.
          apply flipColor_comm_part1.
          apply H.
        }
    + simpl.
      destruct a0.
      * right.
        apply H.
      * destruct a.
        { simpl.
          left.
          apply flipColor_comm_part2.
          apply H.
        }
        { simpl.
          left.
          apply next_inj2.
          apply H.
        }
Qed.

Lemma run1_res : forall (jar : list Pebble), run1 jar = [Red] \/ run1 jar = [Green].
Proof.
  destruct jar.
  - left.
    reflexivity.
  - apply next_singleton.
Qed.

Lemma even_not_odd : forall (n : nat), even n = true -> odd n = false.
Proof.
  intros.
  unfold odd.
  rewrite H.
  reflexivity.
Qed.

Lemma not_even_odd : forall (n : nat), even n = false -> odd n = true.
Proof.
  intros.
  unfold odd.
  rewrite H.
  reflexivity.
Qed.

Lemma run2_even : forall jar : list Pebble, run2 jar = [Red] -> even (count_occ Pebble_eq_dec jar Green) = true.
Proof.
  intros.
  unfold run2 in H.
  destruct (even (count_occ Pebble_eq_dec jar Green)).
  - reflexivity.
  - inversion H.
Qed.

Lemma run2_odd : forall jar : list Pebble, run2 jar = [Green] -> odd (count_occ Pebble_eq_dec jar Green) = true.
Proof.
  intros.
  unfold run2 in H.
  destruct (even (count_occ Pebble_eq_dec jar Green)) eqn:H0.
  - inversion H.
  - apply not_even_odd.
    apply H0.
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

Lemma even_succ_succ_even : forall (n : nat), even n = true -> even (S (S n)) = true.
Proof.
  intros.
  simpl.
  apply H.
Qed.

Lemma odd_succ_succ_odd : forall (n : nat), odd n = true -> odd (S (S n)) = true.
Proof.
  unfold odd.
  intros.
  simpl.
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

Lemma bool_modus_tollens_neg : forall (a b : bool), (a = false -> b = false) -> b = true -> a = true.
Proof.
  intros.
  destruct a; destruct b.
  - apply H0.
  - reflexivity.
  - symmetry.
    apply H.
    reflexivity.
  - apply H0.
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

Lemma succ_even_succ : forall (n : nat), even (S n) = true -> odd n = true.
Proof.
  unfold odd.
  induction n.
  - intro.
    inversion H.
  - intro.
    simpl in H.
    symmetry.
    apply negb_sym.
    simpl (negb true).
    apply (bool_modus_tollens (even (S n)) (negb (even n))).
    + intro.
      apply IHn in H0.
      rewrite H in H0.
      inversion H0.
    + rewrite H.
      reflexivity.
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

Lemma odd_succ_even : forall (n : nat), odd n = true -> even (S n) = true.
Proof.
  intros.
  unfold odd in H.
  symmetry in H.
  apply negb_sym in H.
  simpl in H.
  apply not_even_succ_even.
  apply H.
Qed.

Lemma succ_succ_odd_odd : forall (n : nat), odd (S (S n)) = true -> odd n = true.
Proof.
  unfold odd.
  simpl.
  intros.
  apply H.
Qed.

Lemma succ_odd_even : forall (n : nat), odd (S n) = true -> even n = true.
Proof.
  induction n; try reflexivity.
  intro.
  apply succ_succ_odd_odd in H.
  apply (bool_modus_tollens_neg (even (S n)) (odd n)).
  - intro.
    apply odd_succ_even in H.
    rewrite H in H0.
    inversion H0.
  - apply H.
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

Lemma run2_res : forall (jar : list Pebble), run2 jar = [Red] \/ run2 jar = [Green].
Proof.
  induction jar.
  - left.
    unfold run2.
    reflexivity.
  - destruct IHjar.
    + destruct a.
      * left.
        unfold run2.
        simpl.
        apply run2_even in H.
        rewrite H.
        reflexivity.
      * right.
        apply run2_even in H.
        unfold run2.
        assert (even (count_occ Pebble_eq_dec (Green :: jar) Green) = false).
          { simpl (count_occ Pebble_eq_dec (Green :: jar) Green).
            apply even_succ.
            apply H.
          }
          { rewrite H0.
            reflexivity.
          }
    + destruct a.
      * right.
        rewrite <- H.
        unfold run2.
        reflexivity.
      * left.
        unfold run2.
        apply run2_odd in H.
        assert (even (count_occ Pebble_eq_dec (Green :: jar) Green) = true).
          { simpl (count_occ Pebble_eq_dec (Green :: jar) Green).
            apply not_even_succ_even.
            apply odd_not_even.
            apply H.
          }
          { rewrite H0.
            reflexivity.
          }
Qed.

Lemma bin_mod_toll : forall (jar : list Pebble) (a b : Pebble), (next a jar = [Red] -> next b jar = [Red]) -> next b jar = [Green] -> next a jar = [Green].
Proof.
  intros.
  destruct a; destruct b.
  - apply H0.
  - apply flipColor_comm_part1.
    apply H.
    apply next_inj2.
    apply H0.
  - apply next_inj1.
    apply H.
    apply flipColor_comm_part2.
    apply H0.
  - apply H0.
Qed.

Lemma flipColor_nofix : forall (a : Pebble), ~ a = flipColor a.
Proof.
  destruct a.
  - simpl.
    intro.
    inversion H.
  - simpl.
    intro.
    inversion H.
Qed.

Definition containsEvenGreen (jar : list Pebble) := even (length (filter Pebble_eq_Green_bool jar)) = true.
Definition containsOddGreen (jar : list Pebble) := odd (length (filter Pebble_eq_Green_bool jar)) = true.

Lemma subSubLemma1 : forall (jar : list Pebble), length (filter Pebble_eq_Green_bool (Green :: jar)) = S (length (filter Pebble_eq_Green_bool jar)).
Proof.
  reflexivity.
Qed.

Lemma subSubLemma2 : forall (jar : list Pebble), next Green jar = [Green] -> even (length (filter Pebble_eq_Green_bool jar)) = true.
Proof.
  intro.
  induction (length (filter Pebble_eq_Green_bool jar)); try reflexivity.
  - intro.
Admitted.

Lemma subSubLemma3 : forall (jar : list Pebble), even (length (filter Pebble_eq_Green_bool jar)) = true -> even (length (filter Pebble_eq_Green_bool (Green :: Green :: jar))) = true.
Proof.
  intros.
  apply H.
Qed.

Lemma subSubLemma4 : forall (jar : list Pebble), containsOddGreen (Green :: jar) -> containsEvenGreen jar.
Proof.
  unfold containsEvenGreen, containsOddGreen.
  intros.
  simpl in H.
  apply succ_odd_even.
  apply H.
Qed.

Lemma subSubLemma5 : forall (jar : list Pebble) (a : Pebble), (containsEvenGreen jar -> next a jar = [a]) -> next a jar = [flipColor a] -> containsOddGreen jar.
Proof.
  unfold containsEvenGreen, containsOddGreen.
  induction jar.
  - simpl.
    intros.
    inversion H0.
    inversion H2.
Admitted.

Lemma subLemma1 : forall (jar : list Pebble), even (length (filter Pebble_eq_Green_bool (Green :: jar))) = false -> even (length (filter Pebble_eq_Green_bool jar)) = true.
Proof.
  induction jar.
  - reflexivity.
  - intros.
    destruct a.
    + simpl.
      assert (filter Pebble_eq_Green_bool (Green :: Red :: jar) = filter Pebble_eq_Green_bool (Green :: jar)).
      * reflexivity.
      * rewrite H0 in H.
        apply IHjar.
        apply H.
    + simpl in H.
      rewrite subSubLemma1.
      apply not_even_succ_even.
      apply H.
Qed.

Lemma idk1 : forall (jar : list Pebble) (a : Pebble), next a jar = [a] -> next a (Green :: Green :: jar) = [a].
Proof.
  intros.
  simpl.
  rewrite flipColor_involutive.
  apply H.
Qed.

Lemma idk2 : forall (a : Pebble), next a [] = [a].
Proof.
  reflexivity.
Qed.

Lemma idk3 : forall (jar : list Pebble) (a : Pebble), next a jar = [a] -> next a (Green :: jar) = [flipColor a].
Proof.
  intros.
  simpl.
  destruct a.
  - simpl.
    apply next_inj1.
    apply H.
  - simpl.
    apply next_inj2.
    apply H.
Qed.

Lemma idk4 : forall (jar : list Pebble) (a b : Pebble), next a jar = [b] -> next a (Green :: jar) = [flipColor b].
Proof.
  intros.
  simpl.
  destruct a, b.
  - simpl.
    apply next_inj1, H.
  - simpl.
    apply flipColor_comm_part2, H.
  - simpl.
    apply flipColor_comm_part1, H.
  - simpl.
    apply next_inj2, H.
Qed.

Lemma idk5 : forall (jar : list Pebble) (a b : Pebble), next a jar = [b] -> next a (filter Pebble_eq_Green_bool jar) = [b].
Proof.
  induction jar.
  - intros.
    simpl.
    simpl in H.
    apply H.
  - intros.
    destruct a.
    + simpl.
      apply IHjar, H.
    + simpl.
      simpl in H.
      apply IHjar, H.
Qed.

Lemma idk6 : forall (jar : list Pebble) (a b : Pebble), next a jar = [b] -> next a (Red :: jar) = [b].
Proof.
  intros.
  simpl.
  apply H.
Qed.

Lemma idk7 : forall (jar : list Pebble) (a b : Pebble), next a (filter Pebble_eq_Green_bool jar) = [b] -> next a jar = [b].
Proof.
  induction jar.
  - intros.
    simpl.
    apply H.
  - intros.
    destruct a.
    + simpl.
      simpl in H.
      apply IHjar, H.
    + simpl.
      simpl in H.
      apply IHjar, H.
Qed.

Lemma idk8 : forall (jar : list Pebble) (a b c : Pebble), next a jar = [b] -> next a (c :: jar) = [flipColor b] -> c = Green.
Proof.
  induction jar.
  - intros.
    simpl in H.
    inversion H.
    rewrite <- H2 in H0.
    simpl in H0.
    destruct c.
    + inversion H0.
      exfalso.
      apply (flipColor_nofix a).
      apply H3.
    + reflexivity.
  - intros.
    destruct a0, a, b, c;
    try reflexivity;
    simpl in H, H0;
    rewrite H in H0;
    inversion H0.
Qed.

Lemma idk9 : forall (jar : list Pebble) (a : Pebble), ~ next a jar = next (flipColor a) jar.
Proof.
  induction jar.
  - simpl.
    intros.
    intro.
    inversion H.
    apply (flipColor_nofix a H1).
  - intros.
    intro.
    destruct a0, a;
    simpl in H;
    apply IHjar in H;
    apply H.
Qed.

Lemma idk10 : forall (jar : list Pebble) (a b c : Pebble), next a jar = [b] -> next a (c :: jar) = [b] -> c = Red.
Proof.
  induction jar.
  - intros.
    simpl in H, H0.
    destruct c; try reflexivity.
    rewrite <- H in H0.
    inversion H0.
    symmetry in H2.
    exfalso.
    apply (flipColor_nofix a), H2.
  - intros.
    destruct a0, a, b, c;
    try reflexivity;
    simpl in H, H0;
    rewrite <- H in H0;
    apply idk9 in H0;
    contradiction.
Qed.

Lemma subLemma2 : forall (jar : list Pebble), even (length (filter Pebble_eq_Green_bool jar)) = true -> next Green jar = [Green].
Proof.
  intro.
  destruct (next_res Green jar).
  - intro.
  induction jar; try reflexivity.
Admitted.

Lemma subLemma3 : forall (jar : list Pebble), even (length (filter Pebble_eq_Green_bool jar)) = false -> next Red jar = [Green].
Proof.
  induction jar.
  - simpl.
    intro.
    inversion H.
  - intro.
    destruct a.
    + simpl.
      apply IHjar.
      simpl in H.
      apply H.
    + simpl.
      apply subLemma1 in H.
      simpl in H.
Admitted.

Lemma lemma1 : forall (jar : list Pebble) (a : Pebble), even (length (filter Pebble_eq_Green_bool jar)) = true -> next a jar = [a].
Proof.
  induction jar.
  - reflexivity.
  - intros.
    destruct a.
    + simpl.
      apply IHjar.
      simpl in H.
      apply H.
    + simpl.
      destruct a0.
      * simpl.
        apply flipColor_comm_part2.
        simpl.
        simpl in H.
Admitted.

Lemma lemma2 : forall (jar : list Pebble), run1 jar = [Red] -> next Green jar = [Green].
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

Lemma lemma3 : forall (jar : list Pebble), run1 jar = [Green] -> next Green jar = [Red].
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
