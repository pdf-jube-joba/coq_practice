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

Section lemma.
