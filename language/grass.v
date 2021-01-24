Require Import semantic_model.

(*code*)
Inductive code :=
| Cnil : code
| Ccns : snip -> code -> code
with snip :=
| app : nat -> nat -> snip
| def : nat -> code -> snip.

Instance grass_code : language := {
  code := code
}.

(*grass_machine*)
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

Fixpoint n_th (E : env) (n : nat) : option env_one :=
match E with
| Ecns f E' =>
  match n with | O => Some f | S n' => n_th E' n' end
| Enil => None
end.

Definition one_step (S:stack) : option stack :=
match S with
| Stk (Ccns (app m n) C) E D =>
    let fn := n_th E n in
    let fm := n_th E m in
    match (fn , fm) with
    | (Some (com Cn En) , Some (com Cm Em)) =>
      Some (Stk Cm (Ecns (com Cn En) Em) (Dcns (com C E) D))
    | (_ , _) => None
    end
| Stk (Ccns (def 0 C') C) E D =>
      Some (Stk C (Ecns (com C' E) E) D)
| Stk (Ccns (def (S n) C') C) E D =>
      Some (Stk C (Ecns (com (Ccns (def n C') Cnil) E) E) D)
| Stk Cnil (Ecns f E) (Dcns (com C' E') D) =>
      Some (Stk C' (Ecns f E') D)
| Stk _ _ _ => None
end.

Definition is_stop (m :stack) : bool :=
  match m with
  | Stk (Ccns _ _) _ _ => false
  | Stk  Cnil (Ecns f E) (Dcns f' D) => false
  | Stk _ _ _ => true
  end.

Definition take_value(m :stack) : forall (_ :is_stop m = true), env :=
  (fun _:is_stop m = true =>
  match m with
  | Stk C E D => E
  end).

Theorem H1_stop_means :
  forall m :stack,
  (is_stop m = true) ->  (one_step m = None).
Proof.
  intros m l. destruct m. induction c.
  - induction d;induction e.
    { auto. } { auto. } { auto. }
    { simpl in l. discriminate. }
  - simpl in l. discriminate.
Qed.

Theorem H1_cor :
  forall m :stack,
  (is_stop m = true) -> (one_step m = Some m) \/ (one_step m = None) .
Proof. intros. apply or_intror. apply (H1_stop_means m H). Qed.

Instance grass_machine : machine := {
  state := stack;
  step := one_step;
  stop_or := is_stop;
  stop_means := H1_cor;
}.

(*grass_machine semantic*)

Inductive EQ (e:env) : env -> Prop :=
EQ_refl : EQ e e.
Theorem EQ_ref : forall e:env, EQ e e.
Proof. intro e. apply EQ_refl. Qed.
Theorem EQ_sym : forall (e1 e2 :env), EQ e1 e2 -> EQ e2 e1.
Proof. intros e1 e2 H. destruct H. apply EQ_ref. Qed.
Theorem EQ_trs : forall (e1 e2 e3 :env),
EQ e1 e2 /\ EQ e2 e3 -> EQ e1 e3.
Proof. intros e1 e2 e3 H. destruct H as [H0 H1].
destruct H0. destruct H1. apply EQ_ref. Qed.

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

Theorem H2_two_def_agree_if_stop :
  forall (m :stack) (l :is_stop m = true)(v :env) ,
  has_value m v -> take_value m l = v.
Proof.
  intros m l v H. destruct H.
  - auto.
  - rewrite (H1_stop_means S' l) in H. discriminate.
Qed.

Theorem H3_partiality : forall (m :stack) (v1 v2 :env),
  has_value m v1 /\ has_value m v2 -> v1 = v2.
Proof.
  intros S E1 E2 H.
  induction H as [H0 H1].
  induction H0. apply L0. exact H1.
  induction H1. apply L1 in H. apply False_ind. exact H.
  rewrite <- H1 in H. inversion H. subst. apply IHhas_value. apply H2.
Qed.

Lemma L2 :forall (e1 e2 :env), e1 = e2 -> EQ e1 e2.
Proof. intros e1 e2 H. rewrite H. apply EQ_refl. Qed.

Theorem H3_cor :forall (m :stack)(_:is_halt m) (v1 v2 :env),
  has_value m v1 /\ has_value m v2 -> EQ v1 v2.
Proof. intros. apply L2. exact (H3_partiality m v1 v2 H0). Qed.

Instance ENV : value := {
  supp := env;
  eq := EQ;
  eq_ref := EQ_ref;
  eq_sym := EQ_sym;
  eq_trs := EQ_trs;
}.

Instance grass_machine_semantic
: machine_semantic grass_machine ENV := {
  mchine_has_value :=
    (fun S:state => fun _ :is_halt S => has_value S);
  machine_partiality := H3_cor;
}.

(*code semantic*)

Definition interpret (c:code)(e:env) :stack := Stk c e Dnil.

Instance grass_compile 
: language_compile grass_code grass_machine ENV := {
  compile := interpret;
}.

Definition grass_code_semantic :=
  operational_semantics grass_code ENV
  grass_machine grass_machine_semantic grass_compile.
