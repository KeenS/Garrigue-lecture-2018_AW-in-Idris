% Coqの論理


メモ: 後で使うのでインポートしておく

> import Pruviloj.Core
> %language ElabReflection

1 プログラムの型付け型

...

2 命題論理

...

3 命題と型の対応

...

4 Coq で定理の証明

前述の Curry-Howard 同型のおかげで，Coq の中で直接に命題を書くことができる．その型を
満すプログラムが見付かれば，定理になる．

変数宣言 まずは，準備として論理変数の宣言を行う．parameters という構文を使うと，局所
的な論理変数が宣言できるようになる．括弧の中に宣言を書く．そして，宣言範
囲が終るとインデントを戻す

> namespace Koushin
>   parameters(p, q: Type)

論理式自身は型であると先に説明したが，通常の型の型だった Set と異なり，論理式の型は Prop
になる．普段はあまり影響はないが，区別すると便利なことができる．

命題と証明プログラム

まず，前の二つの恒真式を証明してみよう．
2 つ目は関数適用だけなので，簡単にできる．

>     -- 名前を付けなければならない
>     modusPonens : p -> (p -> q) -> q
>     modusPonens  = \p,pq => pq p
> -- 実際には関数定義と変わらない
> -- λΠ> :printdef modusPonens
> -- modusPonens : (p : Type) -> (q : Type) -> p -> (p -> q) -> q
> -- modusPonens p q = \p, pq => pq p

Idrisだとタプル(P, Q)が論理積に対応する(ほんまか？)

>     andSelf : p -> (p, p)
>     andSelf = \p => (p, p)


作戦 (tactic) の利用

上のように，プログラムを与えることで定理を証明することができる．しかし，複雑な定理に
なると，途中で出て来る命題が煩雑になり，正しいプログラムを書くのが至難の技になる．
通常は，定理は関数と違う定義方法を使う．証明モードに入り，作戦 (tactic) によって証明を
構築していく．各 tactic は導出規則と対応している．

> modusPonens' : {p,q: Type} -> p -> (p -> q) -> q
> modusPonens' = %runElab (do
>   intro `{{Hp}}
>   intro `{{Hpq}}
>   hole <- apply (Var `{{Hpq}}) [True]
>   fill (Var `{{Hp}})
>   solve
> )

