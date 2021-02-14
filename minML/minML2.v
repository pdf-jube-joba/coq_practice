Require Import Init.Nat.

Definition id := nat.

Section syntax.

Inductive opcode :=
| PLUS | MULT | LESSTHAN.

Inductive expression :=
| Var (_:id)
| Nct (_:nat)
| Bct (_:bool)
| Opc (_:opcode) (_ _:expression)
| Ife (_ _ _:expression)
| Bnd (_:nat) (_ _:expression).

End syntax.

Section environment.

Inductive value :=
| vNct (_:nat)
| vBct (_:bool).

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

Definition extend x v (e:environment) := cons (x ,v) e.

End environment.

Section eval.

Definition ap_prim op arg1 arg2 :=
    match op , arg1 , arg2 with
    | PLUS , vNct i1 , vNct i2 => Some (vNct (i1 + i2))
    | MULT , vNct i1 , vNct i2 => Some (vNct (i1 * i2))
    | LESSTHAN , vNct i1 , vNct i2 => Some (vBct (leb i1 i2))
    | _ , _ , _ => None
    end.

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
end.
