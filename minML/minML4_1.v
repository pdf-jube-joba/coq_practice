Require Import Init.Nat.

(*
ここでは次の変更を行う
・primitiveな値、関数をラップする
・実行時エラーである値、errorを追加する
（今は型エラーがないので、適用できないものに適用する事故が起きる
例えば、if 1 then x else y など
*)

Definition id := nat.

Section syntax.

Inductive prim_const :=
| pNct (_:nat) | pBct (_:bool).

Inductive prim_uniop :=
| SUCC | ISZR | NOTB .

Inductive prim_binop :=
| PLUS | MULT | LETN | NAND.

Inductive expression :=
| Variab (_:id)
| Prmcst (_:prim_const)
| Prmuni (_:prim_uniop) (_:expression)
| Prmbin (_:prim_binop) (_ _:expression)
| Ifexpr (_ _ _:expression)
| Letexp (_:id) (_ _:expression)
| Recexp (_ _ :id) (_ _:expression)
| Funexp (_:id) (_:expression)
| Appexp (_ _:expression).

End syntax.

Section environment.

(*なんかlistで通った*)
Inductive value :=
| vPct (_:prim_const)
| vFun (_:id * expression * list (id * value))
| vRec (_:id * id * expression * list (id * value) )
| ERROR .

Definition environment := list (id * value).  

Fixpoint lookup x (e:environment) :=
match e with
| nil => ERROR
| cons h t =>
    let x' := fst h in
    match eqb x x' with
    | true => (snd h)
    | false => lookup x t
    end
end.  

Definition extend x v (e:environment) := cons (x , v) e.

End environment.

Section eval.

Definition conv_uni (op:prim_uniop) (arg :value) :=
    match op , arg with
    | SUCC , vPct (pNct i1) => vPct (pNct (i1 + 1))
    | ISZR , vPct (pNct i1) => vPct (pBct (leb i1 0))
    | NOTB , vPct (pBct b1) => vPct (pBct (negb b1))
    | _ , _ => ERROR
    end.

Definition conv_bin (op:prim_binop) (arg1 arg2:value) :=
    match op , arg1 , arg2 with
    | PLUS , vPct (pNct i1) , vPct (pNct i2) => vPct (pNct (i1 + i2))
    | MULT , vPct (pNct i1) , vPct (pNct i2) => vPct (pNct (i1 + i2))
    | LETN , vPct (pNct i1) , vPct (pNct i2) => vPct (pBct (leb i1 i2))
    | NAND , vPct (pBct i1) , vPct (pBct i2) => vPct (pBct (orb (negb i1) (negb i2)))
    | _ , _ , _ => ERROR
    end.

(*実行時エラーを含めるようにしたため、場合分けが煩雑になる*)
(*エラーが新しく発生するものを含めた場合分け*)
Inductive eval_expression : environment -> expression -> value -> Prop :=
| VariableCase :
    forall E x ,
    eval_expression E (Variab x) (lookup x E)
| PrmconstCase :
    forall E i ,
    eval_expression E (Prmcst i) (vPct i)
| PrmuniopCase :
    forall E u e v,
    eval_expression E e v ->
    eval_expression E (Prmuni u e) (conv_uni u v)
| PrmbinopCase :
    forall E b e1 e2 ,
    forall v1 v2 , eval_expression E e1 v1 /\ eval_expression E e2 v2 ->
    eval_expression E (Prmbin b e1 e2) (conv_bin b v1 v2)
| IfCase :
    forall E e1 e2 e3 ,
    forall v , eval_expression E e1 v ->
    forall t , (match v with | vPct (pBct t) => Some t | _ => None end) = Some t ->
    forall v , eval_expression E (match t with | true => e2 | false => e3 end) v ->
    eval_expression E (Ifexpr e1 e2 e3) v
| IfErrCase :
    forall E e1 e2 e3 ,
    forall v , eval_expression E e1 v ->
    (match v with | vPct (pBct t) => Some t | _ => None end) = None ->
    eval_expression E (Ifexpr e1 e2 e3) ERROR
| LetexpCase :
    forall E x e1 e2 ,
    forall v , eval_expression E e1 v ->
    forall v' , eval_expression (extend x v E) e2 v' ->
    eval_expression E (Letexp x e1 e2) v'
| RecexpCase :
    forall E f x e1 e2 ,
    forall v , eval_expression (extend f (vRec (f , x , e1 , E)) E) e2 v ->
    eval_expression E (Recexp f x e1 e2) v
| FunexpCase :
    forall E x e1 ,
    eval_expression E (Funexp x e1) (vFun (x , e1 , E))
| AppFunCase :
    forall E e1 e2 ,
    forall v1 v2 , (eval_expression E e1 v1 /\ eval_expression E e2 v2) ->
    forall x e3 E1 , v1 = vFun (x , e3 , E1) ->
    forall v , eval_expression (extend x v2 E1) e2 v ->
    eval_expression E (Appexp e1 e2) v
| AppRecCase :
    forall E e1 e2 ,
    forall v1 v2 , (eval_expression E e1 v1 /\ eval_expression E e2 v2) ->
    forall f x e3 E1 , v1 = vRec (f , x , e3 , E1) ->
    forall v , eval_expression (extend f v1 (extend x v2 E1)) e2 v ->
    eval_expression E (Appexp e1 e2) v
| AppErrCase :
    forall E e1 e2 ,
    forall v1 v2 , (eval_expression E e1 v1 /\ eval_expression E e2 v2) ->
    (forall t , v1 = vPct t) \/ v1 = ERROR ->
    eval_expression E (Appexp e1 e2) ERROR.

Theorem partiality :
    forall E e v1 v2 , eval_expression E e v1 /\ eval_expression E e v2 -> v1 = v2.
Proof.
    intros. destruct H.
    generalize dependent E. generalize dependent v1. generalize dependent v2.
    induction e;intros ;inversion H;inversion H0; subst.
    -   reflexivity.
    -   reflexivity.
    -   pose (IHe _ _ _ H5 H10). rewrite e0. reflexivity.
    -   destruct H6. destruct H12.
        pose (IHe1 _ _ _ H1 H3).
        pose (IHe2 _ _ _ H2 H4).
        rewrite e. rewrite e0. reflexivity.
    -   Definition f v :=
        match v with
        | vPct p => match p with
                    | pNct _ => None
                    | pBct t => Some t
                    end
        | _ => None
        end.
        destruct v.
        {
            pose (IHe1 _ _ _ H5 H13).
            destruct p. - discriminate. - destruct b.
            {   apply (IHe2 v2 v1 E). inversion H7. rewrite <- H2 in H8. exact H8.
                assert (f (vPct (pBct true)) = f v3).
                rewrite e. reflexivity. unfold f in H1.
                rewrite <- H1 in H15. inversion H15.
                rewrite <- H3 in H16. exact H16. }
            {   apply (IHe3 v2 v1 E). inversion H7. rewrite <- H2 in H8. exact H8.
                assert (f (vPct (pBct false)) = f v3).
                rewrite e. reflexivity. unfold f in H1.
                rewrite <- H1 in H15. inversion H15.
                rewrite <- H3 in H16. exact H16. } }
        { discriminate. }
        { discriminate. }
        { discriminate. }
    -   pose (IHe1 _ _ _ H5 H14).
        assert (f v = f v3). rewrite e. reflexivity.
        unfold f in H1. rewrite H7 in H1. rewrite H15 in H1. discriminate.
    -   pose (IHe1 _ _ _ H6 H12).
        assert (f v = f v0). rewrite e. reflexivity.
        unfold f in H1. rewrite H7 in H1. rewrite H14 in H1. discriminate.
    -   reflexivity.
    -   pose (IHe1 _ _ _ H6 H13).
        rewrite e in H7. 
        exact (IHe2 _ _ _ H7 H14).
    -   exact (IHe2 _ _ _ H7 H14).
    -   reflexivity.
    -   destruct H3. destruct H10.
        pose (IHe1 _ _ _ H1 H3).
        pose (IHe2 _ _ _ H2 H4).
        inversion e.
        rewrite H6 in H7.
        rewrite H9 in H7.
        rewrite e0 in H7.
        exact (IHe2 _ _ _ H7 H14).
    -   destruct H3. destruct H10.
        pose (IHe1 _ _ _ H1 H3).
        discriminate.
    -   destruct H3. destruct H11.
        destruct H13.
        {   pose (IHe1 _ _ _ H1 H3). rewrite <- e in H5.
            pose (H5 (pBct true)). inversion e0. }
        {   pose (IHe1 _ _ _ H1 H3).
            rewrite H5 in e. inversion e. }
    -   destruct H3. destruct H10.
        pose (IHe1 _ _ _ H1 H3). inversion e.
    -   destruct H3. destruct H10.
        pose (IHe1 _ _ _ H1 H3).
        inversion e.
        pose (IHe2 _ _ _ H2 H4).
        inversion e0.
        rewrite H6 in H7.
        rewrite H8 in H7.
        rewrite H9 in H7.
        rewrite H10 in H7.
        rewrite H5 in H7.
        exact (IHe2 _ _ _ H7 H14).
    -   destruct H3. destruct H11.
        pose (IHe1 _ _ _ H1 H3).
        rewrite <- e in H13.
        destruct H13.
        {   pose (H5 (pBct true)). inversion e0. }
        {   inversion H5. }
    -   destruct H4. destruct H9.
        destruct H6.
        {   pose (H5 (pBct true)). pose (IHe1 _ _ _ H1 H3).
            rewrite e in e0. inversion e0. }
        {   rewrite H5 in H1. pose (IHe1 _ _ _ H1 H3). inversion e. }
    -   destruct H4. destruct H9.
        destruct H6.
        {   pose (IHe1 _ _ _ H1 H3). rewrite e in H5.
            pose (H5 (pBct true)). inversion e0. }
        {   pose (IHe1 _ _ _ H1 H3). rewrite e in H5. inversion H5. }
    -   reflexivity.
Qed.
