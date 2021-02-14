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
| Bnd (_:id) (_ _:expression)
| Rec (_ _ :id) (_ _:expression)
| Fun (_:id) (_:expression)
| App (_ _:expression).


End syntax.

Section environment.

(*
気持ち悪かったので
ML3のProcをvFunに書き換えた。
*)
Inductive value :=
| vNct (_:nat)
| vBct (_:bool)
| vFun (_:id * expression * closure)
| vRec (_:id * id * expression * closure)
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
| RecCase : forall E , forall f x e1 e2 , let e := Rec f x e1 e2 in
    let env := extend f (vRec (f , x , e1 , (Closure E))) E in
    forall v , eval_expression env e2 v -> eval_expression E e v
| FunCase : forall E , forall x1 e1 , let e := Fun x1 e1 in
    eval_expression E e (vFun (x1 , e1 , (Closure E)))
| ApfCase : forall E , forall e1 e2 , let e := App e1 e2 in
    forall v1 v2 , (eval_expression E e1 v1 /\ eval_expression E e2 v2) ->
    forall x e3 E1 , v1 = vFun (x , e3 , (Closure E1)) ->
    forall v , eval_expression (extend x v2 E1) e2 v ->
    eval_expression E e v
| AprCase : forall E , forall e1 e2 , let e := App e1 e2 in
    forall v1 v2 , (eval_expression E e1 v1 /\ eval_expression E e2 v2) ->
    forall f x e3 E1 , v1 = vRec (f , x , e3 , (Closure E1)) ->
    forall v , eval_expression (extend f v1 (extend x v2 E1)) e2 v ->
    eval_expression E e v.

(*  | App(e1,e2) ->
      let funpart = (eval6 e1 env) in
      let arg = (eval6 e2 env) in
        begin
         match funpart with
         | FunVal(x,body,env1) ->
            let env2 = (ext env1 x arg) in
            eval6 body env2
         | RecFunVal(f,x,body,env1) ->
            let env2 = (ext (ext env1 x arg) f funpart) in
            eval6 body env2
         | _ -> failwith "wrong value in App"
        end*)

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
    -   clear e4 e5 e6 e7 e10 e11 e12 e13.
        pose (IHe2 _ _ _ H7 H14).
        exact e.
    -   reflexivity.
    -   destruct H3. destruct H10.
        pose (IHe1 _ _ _ H1 H3).
        inversion e. subst.
        pose (IHe2 _ _ _ H2 H4).
        rewrite e0 in H7.
        exact (IHe2 _ _ _ H7 H14).
    -   destruct H3. destruct H10.
        pose (IHe1 _ _ _ H1 H3).
        discriminate.
    -   destruct H3. destruct H10.
        pose (IHe1 _ _ _ H1 H3).
        discriminate.
    -   destruct H3. destruct H10.
        pose (IHe1 _ _ _ H1 H3).
        inversion e. subst.
        pose (IHe2 _ _ _ H2 H4).
        inversion e0.
        rewrite H5 in H7.
        pose (IHe2 _ _ _ H7 H14).
        exact e3.
Qed.
