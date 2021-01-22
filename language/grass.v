Module grass'.

Section code.

Inductive snip :=
| app : nat -> nat -> snip
| def : nat -> code -> snip
with code :=
| Cnil : code
| Ccns : snip -> code -> code.

End code.

Notation "I ::- C" := (Ccns I C)(at level 60).

Section semantic.

Section machine.

Inductive env_one : Set :=
| com : code -> env -> env_one
with env : Set :=
| Enil  : env
| Ecns : env_one -> env -> env
with dmp : Set :=
| Dnil  : dmp
| Dcns : env_one -> dmp -> dmp.

Inductive stack :=
| Stk : code -> env -> dmp -> stack.

Notation "C &&- E" := (com C E) (at level 60).
Notation "f ::\ E" := (Ecns f E)(at level 60).
Notation "f ::/ D" := (Dcns f D)(at level 60).

Fixpoint n_th (E : env) (n : nat) : option env_one :=
match E with
| f ::\ E' =>
  match n with | O => Some f | S n' => n_th E' n' end
| Enil => None
end.

Definition one_step (S:stack) : option stack :=
match S with
| Stk (app m n ::- C) E D =>
    let fn := n_th E n in
    let fm := n_th E m in
    match (fn , fm) with
    | (Some (Cn &&- En) , Some (Cm &&- Em)) =>
      Some (Stk Cm ((Cn &&- En) ::\ Em) ((C &&- E) ::/ D))
    | (_ , _) => None
    end
| Stk (def 0 C' ::- C) E D =>
      Some (Stk C ((C' &&- E) ::\ E) D)
| Stk (def (S n) C' ::- C) E D =>
      Some (Stk C ((((def n C') ::- Cnil) &&- E) ::\ E) D)
| Stk Cnil (f ::\ E) ((C' &&- E') ::/ D) =>
      Some (Stk C' (f ::\ E') D)
| Stk _ _ _ => None
end.

End machine.

Section operational_semantics.

Inductive has_value : stack -> env -> Prop :=
| HALT : forall (E : env) , has_value (Stk Cnil E Dnil) E
| step : forall (S S': stack) (E : env),
    Some S = one_step S' -> has_value S E -> has_value S' E.


Lemma L0:forall (E1 E2 : env), has_value (Stk Cnil E1 Dnil) E2 -> E1 = E2.
Proof.
  intros E1 E2 H.
  remember (Stk Cnil E1 Dnil) as S.
  induction H.
  injection HeqS; auto.
  subst. simpl in H. destruct E1; inversion H.
Qed.

Lemma L1:forall (S:stack)(E:env), ~ Some S = one_step (Stk Cnil E Dnil).
intros. unfold not. intro H. induction E;simpl in H;discriminate. Qed.

Theorem partiality : forall (S:stack) (E1 E2:env),
  has_value S E1 /\ has_value S E2 -> E1 = E2.
Proof.
  intros S E1 E2 H.
  induction H as [H0 H1].
  induction H0. apply L0. exact H1.
  induction H1. apply L1 in H. apply False_ind. exact H.
  rewrite <- H1 in H. inversion H. subst. apply IHhas_value. apply H2.
Qed.

End operational_semantics.

End semantic.

End grass'.
