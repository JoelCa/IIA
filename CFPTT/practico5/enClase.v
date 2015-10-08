Section EnClase.

Inductive Arbol_bin(A:Set):Set :=
    arbol_nil
  | node: Arbol_bin A -> A -> Arbol_bin A -> Arbol_bin A.


Inductive isomorfismo(A:Set):Arbol_bin A -> Arbol_bin A -> Prop :=
    isomorfismo0 : isomorfismo A (arbol_nil A) (arbol_nil A)
  | isomorfismoS : forall (t1 t2 t1' t2':Arbol_bin A) (a b : A), isomorfismo A t1 t1' -> isomorfismo A t2 t2' -> isomorfismo A (node A t1 a t2) (node A t1' b t2').


Lemma unlema:forall (A:Set) (t1 t2 t3:Arbol_bin A), isomorfismo A t1 t2 -> isomorfismo A t2 t3 -> isomorfismo A t1 t3.
Proof.
  induction t1; intros.
    inversion_clear H in H0.
    assumption.

    inversion_clear H in H0.
    inversion_clear  H0.
    constructor.
      exact((IHt1_1 t1' t1'0) H1 H). (* el "->" NO tiene un constructor? *)

      exact((IHt1_2 t2' t2'0) H2 H3).
Qed.

End EnClase.