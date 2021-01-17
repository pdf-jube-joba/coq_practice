Require Import Nat.

Section lambda_code.

Inductive code :=
| Var : nat -> code
| Abs : nat -> code -> code
| App : code -> code -> code.

End lambda_code.

Section lambda_operational_semantics.

Fixpoint max_L (M : code) : nat :=
match M with
| Var n => n
| Abs n M' => max n (max_L M')
| App M' N' => max (max_L M') (max_L N')
end.

Fixpoint shift (M : code) (b : nat) : code :=
match M with
| Var n => Var (n + b)
| Abs n M' => Abs (n + b) (shift M' b)
| App M' N' => App (shift M' b) (shift N' b)
end.

Fixpoint subst (M : code) (x : nat) (L : code) : code :=
match M with
| Var n =>
  match eqb x n with
  | true => L
  | false => Var n
  end
| Abs n M' => Abs n (subst M' x L)
| App M' N' => App (subst M' x L) (subst N' x L)
end.

Fixpoint redux (M : code) :=
match M with
| Var _ => M
| Abs n M' => Abs n (redux M')
| App M N =>
  let M' := redux M in
  let N' := shift (redux N) (S (max_L M')) in
  (* M'とN'は変数名が被らない*)
  match M' with
  | Var _ => App M' N'
  | Abs x C => subst M' x N'
  | App _ _ => App M' N'
  end
end.

End lambda_operational_semantics.
