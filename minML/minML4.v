Require Import Init.Nat.
​
Definition id:=nat.
​
Section syntax.
​
Inductive opcode :=
| PLUS | MULT | MINUS | LESSTHAN.
​
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
​
​
End syntax.
​
Section environment.
​
(*
気持ち悪かったので
ML3のProcをvFunに書き換えた。
*)
Inductive value :=
| vNct (_:nat)
| vBct (_:bool)
| vFun (_:id * expression * list (id * value))
| vRec (_:id * id * expression * list (id * value)).
​
Definition environment := list (id * value).  
​
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
​
Definition extend x v (e:environment) := cons (x , v) e.
​
End environment.
​
Section eval.
​
Definition ap_prim (op:opcode) (arg1 arg2:value) :=
    match op , arg1 , arg2 with
    | PLUS , vNct i1 , vNct i2 => Some (vNct (i1 + i2))
    | MINUS, vNct i1, vNct i2 => Some (vNct (i1 - i2))
    | MULT , vNct i1 , vNct i2 => Some (vNct (i1 * i2))
    | LESSTHAN , vNct i1 , vNct i2 => Some (vBct (ltb i1 i2))
    | _ , _ , _ => None
    end.
​
Inductive eval_expression : environment -> expression -> value -> Prop :=
| VarCase : forall E , forall x , let e := Var x in 
    forall y , lookup x E = Some y ->
    eval_expression E e y
| NctCase : forall E , forall i , let e := Nct i in
    eval_expression E e (vNct i)
| BctCase : forall E , forall b , let e := Bct b in
    eval_expression E e (vBct b)
| OptCase : forall E , forall op arg1 arg2 v1 v2 v3,
    eval_expression E arg1 v1 -> eval_expression E arg2 v2 ->
    (ap_prim op v1 v2) = Some v3 ->
    eval_expression E (Opc op arg1 arg2) v3
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
    let env := extend f (vRec (f , x , e1 , E)) E in
    forall v , eval_expression env e2 v -> eval_expression E e v
| FunCase : forall E , forall x1 e1 , let e := Fun x1 e1 in
    eval_expression E e (vFun (x1 , e1 , E))
| ApfCase : forall E , forall e1 e2 , let e := App e1 e2 in
    forall v1 v2 , eval_expression E e1 v1 -> eval_expression E e2 v2 ->
    forall x e3 E1 , v1 = vFun (x , e3 , E1) ->
    forall v , eval_expression (extend x v2 E1) e2 v ->
    eval_expression E e v
| AprCase : forall E e1 e2 e3 v2 f x E1 v ,
    let v1 := vRec (f , x , e3 , E1) in 
    eval_expression E e1 v1 -> eval_expression E e2 v2 ->
    eval_expression (extend f v1 (extend x v2 E1)) e3 v ->
    eval_expression E (App e1 e2) v.
​
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
​
Theorem partiality :
    forall e E v1 v2 , eval_expression E e v1 -> eval_expression E e v2 -> v1 = v2.
Proof.
  intros. generalize dependent v2. induction H; intros.
  -
    inversion H0; subst. rewrite H in H3. inversion H3; subst. reflexivity.
  -
    inversion H0; subst. reflexivity.
  -
    inversion H0; subst. reflexivity.
  -
    inversion H2; subst.
    apply IHeval_expression1 in H7; apply IHeval_expression2 in H9; subst.
    rewrite H1 in H10; inversion H10; subst. reflexivity.
  -
    inversion H1; subst; apply IHeval_expression1 in H7; inversion H7; subst.
    apply IHeval_expression2; eauto.
  -
    inversion H1; subst; apply IHeval_expression1 in H7; inversion H7; subst.
    apply IHeval_expression2; eauto.
  -
    inversion H1; subst.
    apply IHeval_expression1 in H7; subst. apply IHeval_expression2; eauto.
  -
    inversion H0; subst. apply IHeval_expression; eauto.
  -
    inversion H0; subst. reflexivity.
  -
    inversion H3; subst; apply IHeval_expression1 in H6; inversion H6; subst.
    apply IHeval_expression2 in H7. subst.
    apply IHeval_expression3 in H11. apply H11.
  -
    inversion H2; subst; apply IHeval_expression1 in H5; inversion H5; subst.
    apply IHeval_expression2 in H7; subst. apply IHeval_expression3; auto.
Qed.
​
Example evalExa :
  eval_expression nil
  (Rec 0 1
          (Ife (Opc LESSTHAN (Nct 0) (Var 1))
                 (Opc MULT (Var 1) (App (Var 0) (Opc MINUS (Var 1) (Nct 1)) ) )
                 (Nct 1)
  ) (App (Var 0) (Nct 3))) (vNct 6).
Proof.
  constructor. eapply AprCase.
  constructor. simpl. reflexivity.
  constructor.
  apply IfTCase. eapply OptCase.
  constructor.
  constructor. simpl. reflexivity.
  compute. reflexivity.
  econstructor.
  constructor. simpl. reflexivity.
  eapply AprCase.
  constructor. simpl. reflexivity.
  eapply OptCase.
  constructor. simpl. reflexivity.
  constructor. compute. reflexivity.
  apply IfTCase. eapply OptCase.
  constructor.
  constructor. simpl. reflexivity.
  compute. reflexivity.
  econstructor.
  constructor. simpl. reflexivity.
  eapply AprCase.
  constructor. simpl. reflexivity.
  eapply OptCase.
  constructor. simpl. reflexivity.
  constructor. compute. reflexivity.
  apply IfTCase. eapply OptCase.
  constructor.
  constructor. simpl. reflexivity.
  compute. reflexivity.
  econstructor.
  constructor. simpl. reflexivity.
  eapply AprCase.
  constructor. simpl. reflexivity.
  eapply OptCase.
  constructor. simpl. reflexivity.
  constructor. compute. reflexivity.
  apply IfFCase. eapply OptCase.
  constructor.
  constructor. simpl. reflexivity.
  compute. reflexivity.
  econstructor.
  compute. reflexivity.
  compute. reflexivity.
  compute. reflexivity.
Qed.
​
​
End eval.
