# 型について
## イントロダクション
　型関連でつまずいたことを書く。
## `not(nat = bool)`について
### 失敗した方法
　これは単純に考えると、`true:bool`だが`true:nat`ではないので簡単に解決できそうである。これにのっとり、trueの型を調べることで実際に証明しようとした。が、次のコードは途中で次の手立てに詰まる。
```
Definition type {A:Set} (x:A) := A.

Theorem l : type true = bool. Proof. trivial. Qed.

Goal not ( nat = bool ).
unfold not. intro H.
generalize l. intro H0.
rewrite <- H in H0.
```
画面は↓
```
1 subgoal
H : nat = bool
H0 : type true = nat
______________________________________(1/1)
False
```
よく考えると、`bool = nat`を仮定しているのだから`type true = nat`でもおかしくはない。したがってここから進みようがない。
### いろいろ試した
　さっきのは`true:nat`を`type true = nat`として表現していたからよくない。なので`type x = A`から`x:A`を取り出せばいい。
```
Definition f :=
(fun {A : Set}{x : A} (l : type x = A ) => x : A).
```
とすれば `(f H0)`は`true:nat`がでてくることになる。が、`(f H0)`はcoqが許してくれない。エラーメッセージは↓
```
In environment
H : nat = bool
H0 : type true = nat
The term "H0" has type "type true = nat"
while it is expected to have type "type true = bool"
(cannot unify "nat" and "bool").
```
一番下の文でunifyできないのが何よりの`not(nat = bool)`の証拠なのに、それをcoq内部の証明に表現する術は他に考え付かなかった。
　結局、「型付けができないので矛盾」はcoqでは表現できなそうだと思った。
### 解決方法と今後の課題
　`not(nat=bool)`自体は元の個数を比べることで証明できたため良かった。しかし、元の個数を考えるという話は一般の場合にも使えるわけではない。明らかに「人間から見て」異なる二つの型が、coq上でも異なることをどうやって示せばいいのだろうか。
## でも`A B:Type,A=B`が示されていても、`x:A`に対して`x:B`とは書けない
　示せないとかではなく、coqの型推論を通らない（それはそう）。解決方法はないので、これを使うのはあきらめて本当にやりたいことに合わせて、色々変えるしかない。似た問題をついでに紹介。
### `A=B`から`x:A`を`x:B`に変えたい。
```
Definition T : forall (A B : Type), A = B -> A -> B.
intros A B l x. rewrite l in x. exact x. Defined.
```
で解決。（A=Bをとり、x:Aをとってx:Bに書き換える。）

## `not (nat = Type)`について
　そもそもそんなものは書けないが、=のimplicitな型推論を外すことで回避できる（Typeだと失敗するだけで、InductiveにA:Typeを定義してもnat=Aが書ける）。つまり`not(@eq Type nat Type)`は書ける（coersionというのによるらしい）。これを悪用して`Set=Type`が示せそうだと思ったが、ちゃんとuniverse inconsistencyではじかれた。
```
Definition type {A:Type} (x:A) := A.

Theorem yabai_lemma: forall(A:Type)(x y:A),
not(x = y)-> (type x) = (type y).
Proof. intros. compute. reflexivity. Qed.

Theorem TypeOfNat : type nat = Set.
Proof. auto. Qed.
Theorem TypeOfType : type Type = Type.
Proof. auto. Qed.

Theorem yaba : not(@eq Type nat Type) -> Set = Type.
Proof.
compute.
intros.
apply yabai_lemma in H.
pose proof TypeOfNat as H0.
pose proof TypeOfType as H1.
```
ここでrewriteするとエラーが出る（いいことだ）。
