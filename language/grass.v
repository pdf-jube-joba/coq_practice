Section grass_code.

Inductive snip :=
| app : nat -> nat -> snip
| def : nat -> code -> snip
with code :=
| Cnil : code
| Ccns : snip -> code -> code.

End grass_code.

Section grass_operational_semantics.

Inductive env_b : Set :=
| com : code -> env -> env_b
with env : Set :=
| Enil  : env
| Ecns : env_b -> env -> env
with dmp : Set :=
| Dnil  : dmp
| Dcns : env_b -> dmp -> dmp.
Inductive stack :=
| Stk : code -> env -> dmp -> stack.

Notation "I ::- C" := (Ccns I C)(at level 60).
Notation "C &&- E" := (com C E) (at level 60).
Notation "f ::\ E" := (Ecns f E)(at level 60).
Notation "f ::/ D" := (Dcns f D)(at level 60).

Fixpoint n_th (E : env) (n : nat) : option env_b :=
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

End grass_operational_semantics.



