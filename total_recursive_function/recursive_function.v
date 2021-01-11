Section lemma.

Fixpoint n_ary (A B :Type) (n:nat) :=
match n with | O => B | S n' => A -> n_ary A B n' end.
Definition total (n:nat) := n_ary nat nat n.

End lemma.

Section Basic_function.

Definition Const : total O := 0.
Definition Successor : total (S O) := (fun x:nat => S x).
Fixpoint projection (n:nat) (i:nat) : total n :=
match n with
| O => 0
| S n' =>
  match i with
  | O => (fun x:nat =>
    (fix C (k:nat) {struct k} : total k :=
    match k with
    | O => x
    | S k' => (fun _:nat => C k')
    end) n' )
  | S i' => (fun _:nat => projection n' i')
  end
end.

End Basic_function.

Section Constructsion.

Section Const_lemma.

Definition phi {A T1 T2:Type}
(F:A -> T1 -> T2) (g:A -> T1) :A -> T2:= (fun x  => ((F x) (g x))).
Definition cmp {X Y Z:Type}
(f:Y->Z) (g:X->Y) : X -> Z:=(fun x:X => f(g x)).
Fixpoint cmp_fold (k:nat) (A T T0:Type)
:(n_ary (A->T) (A->T->T0) k) -> (n_ary (A->T) (A->T0) (S k)):=
match k with
| O => phi
| S k' =>
  (cmp (cmp_fold k' A T T0))
end.
Fixpoint cast (A B:Type) (n:nat)
: (n_ary A B (S n)) -> (n_ary A (A -> B) n):=
match n with
| O => (fun F : A -> B => F)
| S n' =>(fun F : A -> (n_ary A B (S n')) =>
  (fun x : A => ((cast A B n') (F x))) )
end.
Fixpoint U_k (k:nat) (A T T0:Type)
:(n_ary T T0 k) -> (n_ary (A -> T) (A ->T0) k):=
match k with
| O => (fun F:T0 => fun _:A =>F)
| S k' =>(cmp
  (cmp_fold k' A T T0)
  (cmp (U_k k' A T (T->T0)) (cast T T0 k')) )
end.
Fixpoint Um_k (k:nat) (m:nat) (A T T0:Type)
:(n_ary T T0 k) -> (n_ary (n_ary A T m) (n_ary A T0 m) k) :=
match m with
| O => (fun F:(n_ary T T0 k) => F)
| S m' =>(cmp
  (U_k k A (n_ary A T m') (n_ary A T0 m'))
  (Um_k k m' A T T0) )
end.
Fixpoint PU (A B : Type) (k :nat)
: (nat -> A) -> (n_ary A B k) -> B :=
match k with
| O => (fun _ : nat -> A => fun F : B => F)
| S k' =>
  (fun P : nat -> A =>
   fun F : A -> (n_ary A B k') =>
   (PU A B k') (fun (n : nat) => (P (S n))) (F (P O)) )
end.

End Const_lemma.

Section Composition.

Definition COMP (k:nat) (m:nat) := Um_k k m nat nat nat.

End Composition.

Section Primitive_recursion.

Definition PRIM (k:nat)
(f:total k) (g:total (S (S k))) : total (S k) :=
(fix H (x:nat) {struct x} :=
  match x with
  | O => f
  | S x' =>(
    (PU (total k) (total k) (S k))
    (fun i:nat => projection (S k) i x')
    ( (COMP (S (S k)) k) g (H x')))
  end).

End Primitive_recursion.
