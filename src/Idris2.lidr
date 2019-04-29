% Coqの論理


メモ: 後で使うのでインポートしておく

> import Pruviloj.Core
> import Pruviloj.Induction
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

メモ: Idrisでは Elaboration Reflectionというもので証明を構築する。ファイルの先頭に書いた %language ElabReflection がそれを有効にするためのプラグマ。
      まずは証明部分を ?hole と書いて穴が開いた状態にし、Idrisに読み込む。

> --    modusPonens' : p -> (p -> q) -> q
> --    modusPonens' = ?hole

      Emacsのidris-modeだと証明するかと聞いてくるが、それは古い証明フレームワークなので無視し、replから :elab holeを叩く

> -- λΠ> :elab hole

      するとREPLがこうなる

> -- Start proof of Main.Koushin.hole
> -- -Main.Koushin.hole>

     ついでになんか出てくる。これが証明環境。

----------                 Goal:                  ----------
{hole_0} : (p : Type) -> (q : Type) -> p -> (p -> q) -> q


     これはIdrisのバグっぽいのだが、REPLで証明するときのみ暗黙に与えられたpとqが引数に入ってくる (https://github.com/idris-lang/Idris-dev/issues/4556)
     なので手で型pとqを導入する。

> -- -Main.Koushin.hole> intro `{{p}}
> -- -Main.Koushin.hole> intro `{{q}}

    ElaborationはメタプログラミングなのでIdrisの項は特殊な構文で作る。それが `{{ }} 記法。
    ここから証明が書ける

pであるという仮定をHpと名付けて導入する(抽象)

> -- -Main.Koushin.hole> intro `{{Hp}}


----------              Assumptions:              ----------
 p : Type
 q : Type
 Hp : p
----------                 Goal:                  ----------
{hole_0} : (p -> q) -> q

同様に (p -> q) を Hpqと名付けて導入する

> -- -Main.Koushin.hole> intro `{{Hpq}}


----------              Assumptions:              ----------
 p : Type
 q : Type
 Hp : p
 Hpq : p -> q
----------                 Goal:                  ----------
{hole_0} : q

目標を関数Hpqの結果とみなす(適用)

> -- -Main.Koushin.hole> apply (Var `{{Hpq}}) [False]

----------              Other goals:              ----------
{__pi_arg4_501}
----------              Assumptions:              ----------
 p : Type
 q : Type
 Hp : p
 Hpq : p -> q
 {__pi_arg4_501} : p
----------                 Goal:                  ----------
{hole_0} : q =?= Hpq _

メモ: introでは変数の導入だったので生の `{{ }} だったがここでは変数の参照なのでVarで包む
メモ: apply (Var `{{Hpq}}) [False] に渡している `[False]` はよくわかってない。ドキュメントには引数をunifyするかどうかと書いてあるが…。ひとまずHpqの引数の数だけBooleanを並べる


メモ: Idrisでは余計なHoleが出来るので潰す作業が要る

> -- -Main.Koushin.hole> solve


----------              Assumptions:              ----------
 p : Type
 q : Type
 Hp : p
 Hpq : p -> q
----------                 Goal:                  ----------
{__pi_arg4_501} : p


> -- -Main.Koushin.hole> hypothesis


hole: No more goals.

> -- -Main.Koushin.hole> :qed
> -- Proof completed!
> -- End proof of Main.Koushin.hole


実際の証明をもう一度みよう．

メモ: IdrisではREPLとソースコードで書かれるものが変わる。
      1. 先程説明したとおりREPLでは余計なpとqの導入がある
      2. 証明の置き方が異なる
         * REPLでは:elabで証明を開始し、:qedで証明を完了した
         * ソースコードでは do .. に証明を書き、 それを %runElab で走らせる

>     modusPonens' : p -> (p -> q) -> q
>     modusPonens' = %runElab (do
>       intro `{{Hp}}
>       intro `{{Hpq}}
>       apply (Var `{{Hpq}}) [False]
>       solve
>       hypothesis
>     )



andselfについて同じことをする．

> --    andSelf' : p -> (p, p)
> --    andSelf' = ?hole

> -- λΠ> :elab hole
> -- Start proof of Main.Koushin.hole
> -- -Main.Koushin.hole>

----------                 Goal:                  ----------
{hole_0} : (p : Type) -> Type -> p -> (p, p)


メモ: modusPonens'と同様にREPLではpを導入する

> -- -Main.Koushin.hole2> intro `{{p}}


----------              Assumptions:              ----------
 p : Type
----------                 Goal:                  ----------
{hole_0} : Type -> p -> (p, p)


メモ: 謎のパラメータ Typeがある。恐らくタプル由来の型なので適当にpairなどと名付けておく



> -- -Main.Koushin.hole2> intro `{{pair}}


----------              Assumptions:              ----------
 p : Type
 pair : Type
----------                 Goal:                  ----------
{hole_0} : p -> (p, p)



> -- -Main.Koushin.hole2> intro `{{Hp}}


----------              Assumptions:              ----------
 p : Type
 pair : Type
 Hp : p
----------                 Goal:                  ----------
{hole_0} : (p, p)


論理積の導入(/\導入)

> -- -Main.Koushin.hole2> construct

ゴールとOther goalsで2つ出来た

----------              Other goals:              ----------
{b_504}
----------              Assumptions:              ----------
 p : Type
 pair : Type
 Hp : p
----------                 Goal:                  ----------
{a_503} : p

順番に解いていく。まずは1つ目

> -- -Main.Koushin.hole2> hypothesis


----------              Assumptions:              ----------
 p : Type
 pair : Type
 Hp : p
----------                 Goal:                  ----------
{b_504} : p

同様に2つ目

> -- -Main.Koushin.hole2> hypothesis

hole: No more goals.

> -- -Main.Koushin.hole> :qed
> -- Proof completed!
> -- End proof of Main.Koushin.hole


>     andSelf' : p -> (p, p)
>     andSelf' = %runElab (do
>       intro `{{Hp}}
>       construct
>       hypothesis
>       hypothesis
>     )

> -- 実際の定義は前とあまり変わらないが必要な変数が定義に挿入される
> -- λΠ> :printdef andSelf'
> -- andSelf' : (p : Type) -> Type -> p -> (p, p)
> -- andSelf' p q = \Hp => (Hp, Hp)


否定に関する定理

> namespace Negation
>   parameters(p, q: Type)
>     -- orに相当するのはEither
>     deMorgan : (Not (Either p q) ) -> (Not p, Not q)
>     deMorgan = %runElab (do
>       intro `{{Hnpq}}
>       -- Coq     -   Idris
>       -- split       construct
>       -- ;       -   `andThen
>       --
>       -- Idrisではintroの前にattackしとかないとエラーになる。
>       -- 複数のtacticの合成は安直には`do`を使う。
>       construct `andThen` (do
>         attack
>         intro `{{Hq}})
>       -- 別解として `*>` を使う方法もある
>       -- construct `andThen` (attack *> intro `{{Hq}})
>
>       -- このあたりはtacticのあとに都度solveが必要なのでsolveを1行にまとめる
>       apply (Var `{{Hnpq}}) [False]; solve
>       -- Coqのleft相当。Idrisの関数 `Left` を適用しているだけだが、型を明示的に示さないといけないので長い。
>       apply `(Right {a=~(Var `{{p}})} {b=~(Var `{{q}})}) [False]; solve
>       hypothesis; solve
>       -- 以後同様。
>       apply (Var `{{Hnpq}}) [False]; solve
>       apply `(Left {a=~(Var `{{p}})} {b=~(Var `{{q}})}) [False]; solve
>       hypothesis; solve
>     )



しかし，双対的な定理 `(:(P^Q) :P_ :Q)`は直観主義論理ではなりたたない．????コマンドによって二重否定の除去を仮定すると証明できる．

メモ: 仮説、公理を定義するコマンドが分からなかったのでbelieve_meで無理やりclassicを定義する

>     classic : Not (Not a) -> a
>     classic = believe_me

>     deMorgan' : (Not (p, q) ) -> Either (Not p) (Not q)
>     deMorgan' = %runElab (do
>       intro `{{Hnpq}}
>       apply `(classic {p=~(Var `{{p}})} {q=~(Var `{{q}})} {a=(Either (Not ~(Var `{{p}})) (Not ~(Var `{{q}})))}) [False]; solve
>       attack
>       intro `{{Hnnpq}}
>       apply (Var `{{Hnpq}}) [False]; solve
>       -- idris だと型を明示しないといけない関係でconstruct `andThen` (apply classic)と書けない
>       construct
>       apply `(classic {p=~(Var `{{p}})} {q=~(Var `{{q}})}{a=~(Var `{{p}})}) [False];  solve
>       attack
>       intro `{{Hnp}}
>       apply (Var `{{Hnnpq}}) [False]; solve
>       apply `(Left {a=(Not ~(Var `{{p}}))} {b=(Not ~(Var `{{q}}))}) [False]; solve
>       hypothesis; solve
>       apply `(classic {p=~(Var `{{p}})} {q=~(Var `{{q}})}{a=~(Var `{{q}})}) [False]; solve
>       attack
>       intro `{{Hnq}}
>       apply (Var `{{Hnnpq}}) [False]; solve
>       apply `(Right {a=(Not ~(Var `{{p}}))} {b=(Not ~(Var `{{q}}))}) [False]; solve
>       hypothesis; solve; solve)


仮定を破壊する

Coqの帰納的データ型に対して，値を破壊しながら中身を取り出すというtacticが便利である．直接に対応する論理規則はないが，当然ながら他の論理規則から同じ結果を導くことは可能である．

> namespace Destruct
>   parameters(p, q : Type)
>     andComm : (p, q) -> (q, p)
>     andComm = %runElab (do
>       intro `{{Hpq}}
>       -- タプル専用 split .. as .. 相当のものとして both がある
>       both (Var `{{Hpq}}) `{{Hp}} `{{Hq}}
>       construct `andThen` hypothesis
>       pure ())

-- Eitherの分解どうするの？？？
-- >     orComm : Either p q -> Either q p
-- >     orComm = ?hole


練習問題4.1以下の定理をCoqで証明せよ

> namespace Idris2
>   parameters(p, q, r: Type)
>     impTrans : (p -> q) -> (q -> r) -> p -> r
>     impTrans = %runElab (do
>       intro `{{Hpq}}
>       intro `{{Hqr}}
>       intro `{{Hp}}
>       apply (Var `{{Hqr}}) [False]; solve
>       apply (Var `{{Hpq}}) [False]; solve
>       hypothesis
>     )

>     notFalse : Not Void
>     notFalse = %runElab (do
>       intro `{{Hvoid}}
>       hypothesis
>     )

>     doubleNeg : p -> Not (Not p)
>     doubleNeg = %runElab (do
>       intro `{{Hp}}
>       intro `{{Hnp}}
>       apply (Var `{{Hnp}}) [False]; solve
>       hypothesis
>     )

>     contraposition : (p -> q) -> Not q ->Not p
>     contraposition = %runElab (do
>       intro `{{Hpq}}
>       intro `{{Hnq}}
>       intro `{{Hp}}
>       apply (Var `{{Hnq}}) [False]; solve
>       apply (Var `{{Hpq}}) [False]; solve
>       hypothesis
>     )


>     andAssoc : (p, (q, r)) -> ((p, q), r)
>     andAssoc = %runElab (do
>       intro `{{Hpqr}}
>       both (Var `{{Hpqr}}) `{{Hp}} `{{Hqr}}
>       both (Var `{{Hqr}}) `{{Hq}} `{{Hr}}
>       construct `andThen` (try hypothesis)
>       construct `andThen` (hypothesis)
>       pure ()
>     )

-- >     andDistr : (p, Either q r) -> Either (p, q) (p, r)
-- >     andDistr = %runElab (do
-- >       intro `{{Hpqr}}
-- >       both (Var `{{Hpqr}}) `{{Hp}} `{{Hqr}}
-- >       -- Eitherをばらせない
-- >     )


>     absurd : p -> Not p -> q
>     absurd = %runElab (do
>       intro `{{Hp}}
>       intro `{{Hnp}}
>       apply `(void {a=~(Var `{{q}})}) [False]; solve
>       apply (Var `{{Hnp}}) [False]; solve
>       hypothesis)

