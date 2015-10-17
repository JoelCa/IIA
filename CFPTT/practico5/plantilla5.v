(* Práctico 5 *)

(* Ejercicio 1 *)
Require Import Coq.Lists.List.

Section Ejercicio1.

Inductive LE : nat -> nat -> Prop :=
  | Le_O : forall n : nat, LE 0 n
  | Le_S : forall n m : nat, LE n m -> LE (S n) (S m).

(* NO acepta "cons A a x" *)
Inductive Mem (A : Set) (a : A) : list A -> Prop :=
  | here : forall x : list A, Mem A a (cons a x)
  | there : forall x : list A, Mem A a x -> forall b : A, Mem A a (cons b x).

(* 1.1 *)
Theorem not_sn_le_o: forall n:nat, ~ LE (S n) O.
Proof.
  unfold not; intros.
   inversion H.
Qed.

(* 1.2 *)
(* NO acepta "nil A" *)
Theorem nil_empty: forall (A:Set) (a:A), ~ Mem A a nil.
Proof.
  unfold not; intros; inversion H.
Qed.

(* 1.3 *)
Theorem ej1_3 : ~LE 4 3.
Proof.
  unfold not; intro H.
  inversion_clear H; inversion_clear H0; inversion_clear H; inversion_clear H0.
Qed.

(* 1.4 *)
Theorem ej1_4 : forall (n:nat), ~LE (S n) n.
Proof.
  unfold not; induction n; intro H.
    inversion H.

    apply IHn.
    inversion_clear H; assumption.
Qed.

(* 1.5 *)
Theorem ej1_5 : forall (n m r:nat), LE n m /\ LE m r -> LE n r.
Proof.
  induction n; intros.
    exact (Le_O r).

    elim H; intros; clear H.
    inversion H0.
    rewrite <- H3 in H1.
    inversion H1.
    assert (LE n m1); [exact ((IHn m0 m1) (conj H2 H5))|idtac].
    exact ((Le_S n m1) H7).
Qed.

(* 1.6 *)
(* Tengo que definir el pertenece y el append? Puedo usar los de la librería *)
(* "pertenece a la concatenación de esta lista con cualquier otra", tengo que
considerar las dos concatenaciones posibles? NO *)
Theorem ej1_6 : forall (A:Set) (a:A) (l1 l2:list A), In a l1 -> In a (app l1 l2).
Proof.
  induction l1.
    intros.
    simpl in H.
    elim H.

    intros.
    simpl in *.
    elim H; intro H'.
      left; assumption.

      right; exact ((IHl1 l2) H').
Qed.

End Ejercicio1.

(* Ejercicio 2 *)
Section Ejercicio2.

Inductive bintree(A:Set):Set :=
    btree_nil
  | node: bintree A -> A -> bintree A -> bintree A.

Inductive isomorfismo(A:Set):bintree A -> bintree A -> Prop :=
    isomorfismoB : isomorfismo A (btree_nil A) (btree_nil A)
  | isomorfismoI : forall (t1 t2 t1' t2':bintree A) (a b : A), isomorfismo A t1 t1' -> isomorfismo A t2 t2' -> isomorfismo A (node A t1 a t2) (node A t1' b t2').

Fixpoint inverse (A:Set) (t:bintree A):bintree A :=
  match t with
  | btree_nil => btree_nil A
  | node t1 a t2 => node A (inverse A t2) a (inverse A t1)
  end.

(* 2.1 *)
Theorem ej2_1 : forall (A:Set) (t:bintree A), ~t = btree_nil A -> ~isomorfismo A (btree_nil A) t.
Proof.
  unfold not in *; intros.
  inversion H0.
  apply H; symmetry; assumption.
Qed.

(* 2.2 *)
Theorem ej2_2 : forall (A:Set) (t1 t2 t3 t4:bintree A) (a b:A), isomorfismo A (node A t1 a t2) (node A t3 b t4) -> isomorfismo A t1 t3 /\ isomorfismo A t2 t4.
Proof.
  intros.
  inversion_clear H.
  split; assumption.
Qed.

(* 2.3 *)
Theorem ej2_3 : forall (A:Set) (t1 t2 t3:bintree A), isomorfismo A t1 t2 /\ isomorfismo A t2 t3 -> isomorfismo A t1 t3.
Proof.
  induction t1.
    intros.
    elim H; intros; clear H.
    inversion H0.
    rewrite <- H2 in H1.
    inversion H1.
    exact (isomorfismoB A).
      intros.
      elim H; intros; clear H.
      inversion H0.
      rewrite <- H3 in H1.
      inversion_clear H1.
      assert (isomorfismo A t1_1 t1'0).
      exact ((IHt1_1 t1' t1'0) (conj H5 H7)).
      assert (isomorfismo A t1_2 t2'0).
      exact ((IHt1_2 t2' t2'0) (conj H6 H8)).
      exact ((isomorfismoI A t1_1 t1_2 t1'0 t2'0 a b0) H1 H9).
Qed.

(* 2.4 *)
Theorem ej2_4 : forall (A:Set) (t1 t2:bintree A), isomorfismo A t1 t2 -> isomorfismo A (inverse A t1) (inverse A t2).
Proof.
  induction t1.
    intros.
    inversion_clear H.
    simpl; exact (isomorfismoB A).

    intros.
    inversion_clear H.
    assert (isomorfismo A (inverse A t1_1) (inverse A t1')); [exact ((IHt1_1 t1') H0)|idtac].
    assert (isomorfismo A (inverse A t1_2) (inverse A t2')); [exact ((IHt1_2 t2') H1)|idtac].
    simpl.
    exact ((isomorfismoI A (inverse A t1_2) (inverse A t1_1) (inverse A t2') (inverse A t1') a b) H2 H).
Qed.

End Ejercicio2.

(* Ejercicio 3 *)
Section Ej5_3.

Variable A : Set.

Parameter equal : A -> A -> bool.

Axiom equal1 : forall x y : A, equal x y = true -> x = y.

Axiom equal2 : forall x : A, equal x x <> false.

Inductive List : Set :=
  | nullL : List
  | consL : A -> List -> List.

Inductive MemL (a : A) : List -> Prop :=
  | hereL : forall x : List, MemL a (consL a x)
  | thereL : forall x : List, MemL a x -> forall b : A, MemL a (consL b x).

(* 3.1 *)
Inductive isSet : List -> Prop :=
  | isSetB : isSet nullL
  | isSetI : forall (l:List) (a:A), ~MemL a l -> isSet l -> isSet (consL a l).

(* 3.2 *)
Fixpoint deleteAll (a:A) (l:List):List :=
  match l with
  | nullL => nullL
  | consL x l' => if equal x a then deleteAll a l' else consL x (deleteAll a l')
  end.

(* 3.3 *)
(* equal se podría haber definido inductivamente? *)

Lemma equal_lema1 : forall (a b:A), a = b -> equal a b = true.
Proof.
  intros.
  assert(equal a b = true \/ equal a b = false).
  destruct (equal a b); [left|right]; reflexivity.
  elim H0; intro H'; clear H0.
    assumption.
    rewrite H'.
    assert (False -> false = true); [intro H''; elim H''|idtac].
    apply H0; rewrite H in H'.
    exact ((equal2 b) H').
Qed.


Theorem equal_lema2 : forall (a b:A), equal a b = false -> ~a=b.
Proof.
  unfold not; intros.
  assert (equal a b = true); [exact ((equal_lema1 a b) H0)|idtac].
  rewrite H in H1; discriminate H1.
Qed.

Lemma DeleteAllNotMember : forall (l : List) (x : A), ~ MemL x (deleteAll x l).
Proof.
  unfold not; induction l; intros.
    simpl in H.
    inversion H.

    simpl in H.
    assert(equal a x = true \/ equal a x = false). (* incluí esto, por que el destruct no incluye igualdades *)
    destruct (equal a x); [left|right]; reflexivity.
    elim H0; intro H'; clear H0; rewrite H' in H; simpl in H.
      apply (IHl x); assumption.

      apply (IHl x).
      assert (~a=x); [exact((equal_lema2 a x) H')|idtac].
      inversion H.
        absurd (x=a); [apply not_eq_sym|idtac];assumption.

        assumption.
Qed.

(* 3.4 *)
Fixpoint delete (a:A) (l:List):List :=
  match l with
  | nullL => nullL
  | consL x l' => if equal x a then l' else consL x (delete a l')
  end.


(* 3.5 *)
Lemma DeleteNotMember : forall (l : List) (x : A), isSet l -> ~ MemL x (delete x l).
Proof.
  unfold not; induction l; intros.
    simpl in H0; inversion H0.

    simpl in H0.
    assert(equal a x = true \/ equal a x = false). (* incluí esto, por que el destruct no incluye igualdades *)
    destruct (equal a x); [left|right]; reflexivity.
    elim H1; intro H'; clear H1; rewrite H' in H0; simpl in H0.
    assert (a = x); [exact ((equal1 a x) H') |idtac].
    rewrite H1 in H.
    inversion_clear H.
    absurd (MemL x l); assumption.
    apply (IHl x).
      inversion_clear H; assumption.

      assert (~a=x); [exact((equal_lema2 a x) H')|idtac].
      inversion H0.
        absurd (x=a); [apply not_eq_sym|idtac];assumption.

        assumption.
Qed.

End Ej5_3.























