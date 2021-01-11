Fixpoint n_ary (A T:Type) (n:nat) : Type :=
match n with
| O => T
| S n' => A ->(n_ary A T n')
end.

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

Theorem l:forall (A T T0:Type)
(F:n_ary T T0 4) (g1 g2 g3 g4:n_ary A T 2) (x1 x2:A),
(Um_k 4 2 A T T0) F g1 g2 g3 g4 x1 x2 =
F (g1 x1 x2) (g2 x1 x2) (g3 x1 x2) (g4 x1 x2).
intros. 
  unfold Um_k. unfold U_k. unfold cmp_fold.
  unfold cast. simpl. unfold cmp. unfold phi.
reflexivity. Qed.
