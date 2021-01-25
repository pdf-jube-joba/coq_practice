Section s.
Variable A : Type.
Fixpoint n_ary (T1 T2 : Type) (n : nat) :=
match n with | O => T2 | S n' => T1 -> (n_ary T1 T2 n') end.
Variable G : forall n : nat , n_ary A A n.

(*
make Inductive definition like
P :=
| Ins (n:nat) : forall g_1 ... g_n , (P g_1) /\ .. /\ (P g_n) -> P (G n g1 ... gn) .
*)

Fixpoint L0 {T1 T2 T3 : Type} (n : nat)
: (n_ary T1 T2 n) -> (T2 -> T3) -> (n_ary T1 T3 n) :=
match n with
| O => (fun b : T2 => fun f : T2 -> T3 => f b)
| S n' => (fun a : T1 -> (n_ary T1 T2 n') =>
    fun f : T2 -> T3 => fun x : T1 => (L0 n') (a x) f )
end.
Fixpoint L1 {T : Type} (n : nat) (F : T -> Prop)
: (n_ary T Prop n) :=
match n with
| O => True
| S n' => (fun a : T =>
    (L0 n') (L1 n' F) (and (F a)))
end.
Fixpoint L2 {T1 : Type} (n : nat)
: (n_ary T1 Prop n) -> (n_ary T1 Prop n) -> Prop :=
match n with
| O => (fun P1 : Prop => fun P2 : Prop => (P1 -> P2))
| S n' => (fun P1 P2 : T1 -> (n_ary T1 Prop n') =>
    forall  x : T1 , L2 n' (P1 x) (P2 x))
end.
(* fail
Inductive P : A -> Prop :=
| Bas : P (G 0)
| Ins (n : nat) : L2 n (L1 n P) (L0 n (G n) P).
*)
