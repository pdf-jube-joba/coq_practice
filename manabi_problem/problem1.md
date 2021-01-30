# 原始再帰的関数を作る際にはまった問題（未解決）
## 前提
n項関数を`A-> ... n ... -> A -> B`としてとらえている。具体的には、
```
Fixpoint n_ary (T1 T2 : Type) (n : nat) :=
match n with | O => T2 | S n' => T1 -> (n_ary T1 T2 n') end.
```
である。

## 問題
`A:Type`と`n項関数G:forall`が与えられたときに、InductiveなPropとして次のようなものを作りたい。（ここでG 0 : Aであることに注意）
```
Inductive P : A -> Prop :=
| S0 : P (G 0)
| S1 : forall (x1:A), (P x1) -> (P (G 1 x1))
| S2 : forall (x1 x2:A), (P x1)/\(P x2) -> (P (G 2 x1 x2))
| S3 : forall (x1 x2 x3:A), (P x1)/\(P x2)/\(P x3) -> (P (G 3 x1 x2 x3))
...
```
## 失敗した方法
```
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
```
こうすると、`L2 n (L1 n P) (L0 n (G n) P)`は
`forall (x1 ... xn :A),(P x1)/\.../\(P xn) -> P (G n x1 ... xn)`になるが
次は失敗する
```
Inductive P : A -> Prop :=
| S (n : nat) : L2 n (L1 n P) (L0 n (G n) P).
```
エラーは
```
In environment
A : Type
G : forall n : nat, n_ary A A n
P : A -> Prop
n : nat
Unable to unify
 "(fix L2 (T1 : Type) (n : nat) {struct n} :
       n_ary T1 Prop n -> n_ary T1 Prop n -> Prop :=
     match
       n as n0
       return (n_ary T1 Prop n0 -> n_ary T1 Prop n0 -> Prop)
     with
     | 0 => fun P1 P2 : Prop => P1 -> P2
     | S n' =>
         fun P1 P2 : T1 -> n_ary T1 Prop n' =>
         forall x : T1, L2 T1 n' (P1 x) (P2 x)
     end) A n (L1 n P) (L0 n (G n) P)"
with "P ?a".
```
とでるが謎に?aが出てるのは(strictly) positivityのための計算だと思われる。
小さめの例として、
```
Variable A : Type.
Variable F : (A -> Prop) -> (A -> Prop).
Inductive P : A -> Prop :=
| S : forall (a:A), (F P) a.
```
が同じ問題だと思われる。
