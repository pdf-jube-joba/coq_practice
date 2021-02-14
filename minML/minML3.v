Require Import Init.Nat.

Definition id:=nat.

Section syntax.

Inductive opcode :=
| PLUS | MULT | LESSTHAN.

Inductive expression :=
| Var (_:id)
| Nct (_:nat)
| Bct (_:bool)
| Opc (_:opcode) (_ _:expression)
| Ife (_ _ _:expression)
| Bnd (_:nat) (_ _:expression)
| Fun (_:id) (_:expression)
| App (_ _:expression).

End syntax.

Section environment.

(*
Inductive value :=
...Proc (_:id*expression*(list(id*value))
はpositivityで通らないので、
あらためて(list (id*value))を置きなおしている。
*)

Inductive value :=
| vNct (_:nat)
| vBct (_:bool)
| Proc (_:id * expression * closure)
with closure :=
| Closure : list (id * value) -> closure.

Definition environment := list (id * value).  

Fixpoint lookup x (e:environment) :=
match e with
| nil => None
| cons h t =>
    let x' := fst h in
    match eqb x x' with
    | true => Some (snd h)
    | false => lookup x t
    end
end.  

Definition extend x v (e:environment) := cons (x , v) e.

End environment.

Section eval.

Definition ap_prim (op:opcode) (arg1 arg2:value) :=
    match op , arg1 , arg2 with
    | PLUS , vNct i1 , vNct i2 => Some (vNct (i1 + i2))
    | MULT , vNct i1 , vNct i2 => Some (vNct (i1 * i2))
    | LESSTHAN , vNct i1 , vNct i2 => Some (vBct (leb i1 i2))
    | _ , _ , _ => None
    end.

(*
coqだとうまく書かないと通らない
原因は eval E (App e1 e2)=> eval new_E body
where (eval e2) = (x1,body,C1)のところ
型なしのためfunとappでYコンビネータができそうなので、
これは実際停止しない。
*)
Fail
Fixpoint eval_expression (E:environment) (e:expression) : option value :=
match e with
| Var x => lookup x E
| Nct i => Some (vNct i)
| Bct b => Some (vBct b)
| Opc op arg1 arg2 =>
    let v1 := eval_expression E arg1 in
    let v2 := eval_expression E arg2 in
    match v1 , v2 with
    | Some i1 , Some i2 => ap_prim op i1 i2
    | _ , _ => None
    end 
| Ife arg1 arg2 arg3 => None
| Bnd i1 e1 e2 =>
    let e1' := eval_expression E e1 in
    match e1' with
    | Some v1 => eval_expression (extend i1 v1 E) e2
    | None => None
    end
| Fun x1 e1 => Some (Proc (x1 , e1 , (Closure E)))
| App e1 e2 =>
    let e1' := eval_expression E e1 in
    let e2' := eval_expression E e2 in
    match e1' , e2' with
    | Some v1 , Some v2 =>
        match v1 with
        | Proc (x1 , body , (Closure C1)) =>
            let new_E := extend x1 v2 C1 in
            eval_expression new_E body 
        | _ => None
        end
    | _ , _ => None
    end
end.

(*代わりに関係で表す奴にする*)

Inductive eval_expression : environment -> expression -> value -> Prop :=
| VarCase : forall E , forall x , let e := Var x in 
    forall y , lookup x E = Some y ->
    eval_expression E e y
| NctCase : forall E , forall i , let e := Nct i in
    eval_expression E e (vNct i)
| BctCase : forall E , forall b , let e := Bct b in
    eval_expression E e (vBct b)
| OptCase : forall E , forall op arg1 arg2 , let e := Opc op arg1 arg2 in
    forall v1 v2 , eval_expression E arg1 v1 /\ eval_expression E arg2 v2 ->
    forall v3 , (ap_prim op v1 v2) = Some v3 ->
    eval_expression E e v3
| IfTCase : forall E , forall e1 e2 e3 , let e := Ife e1 e2 e3 in
    eval_expression E e1 (vBct true) ->
    forall v , eval_expression E e2 v ->  eval_expression E e v
| IfFCase : forall E , forall e1 e2 e3 , let e := Ife e1 e2 e3 in
    eval_expression E e1 (vBct false) ->
    forall v , eval_expression E e3 v ->  eval_expression E e v
| BndCase : forall E , forall x e1 e2 , let e := Bnd x e1 e2 in
    forall v , eval_expression E e1 v ->
    forall v' , eval_expression (extend x v E) e2 v' -> eval_expression E e v'
| FunCase : forall E , forall x1 e1 , let e := Fun x1 e1 in
    eval_expression E e (Proc (x1 , e1 , (Closure E)))
| AppCase : forall E , forall e1 e2 , let e := App e1 e2 in
    forall v1 v2 , (eval_expression E e1 v1 /\ eval_expression E e2 v2) ->
    forall x e3 E1 , v1 = Proc (x , e3 , (Closure E1)) ->
    forall v , eval_expression (extend x v2 E1) e2 v -> eval_expression E e v.

Theorem partiality :
    forall E e v1 v2 , eval_expression E e v1 /\ eval_expression E e v2 -> v1 = v2.
Proof.
    intros. destruct H.
    generalize dependent E. generalize dependent v1. generalize dependent v2.
    induction e;intros ;inversion H;inversion H0; subst.
    -   rewrite H3 in H7. inversion H7. reflexivity.
    -   reflexivity.
    -   reflexivity.
    -   destruct H6. destruct H13.
        pose (IHe1 _ _ _ H1 H3).
        pose (IHe2 _ _ _ H2 H4).
        rewrite e in H7. rewrite e8 in H7.
        rewrite H7 in H14. inversion H14. reflexivity.
    -   exact (IHe2 _ _ _ H7 H14).
    -   pose (IHe1 _ _ _ H6 H13). discriminate.
    -   pose (IHe1 _ _ _ H6 H13). discriminate.
    -   exact (IHe3 _ _ _ H7 H14).
    -   pose (IHe1 _ _ _ H6 H13). rewrite e in H7.
        exact (IHe2 _ _ _ H7 H14).
    -   reflexivity.
    -   destruct H3. destruct H10.
        pose (IHe1 _ _ _ H1 H3).
        inversion e. subst.
        pose (IHe2 _ _ _ H2 H4).
        rewrite e0 in H7.
        exact (IHe2 _ _ _ H7 H14).
Qed. 