-- 定義と関数

-- 定義
one : Nat
one = 1

-- one : Nat
-- one = 1
-- 再定義はできない
-- - + Errors (1)
--  `-- (no file) line 0 col -1:
--      Idris1.idr:7:5:Main.one already defined

-- Idrisだと型を書く必要がある
-- one' = 1
-- - + Errors (1)
--  `-- Idris1.idr line 15 col 0:
--      No type declaration for Main.one'

-- 定義の確認はREPLで `:printdef` を使う
-- λΠ> :printdef one
-- one : Nat
-- one = fromInteger 1

-- 以後 `λΠ>` で始まるのがREPLへの入力
-- 続く行が出力


--関数の定義
double : Nat -> Nat
double x = x + x

-- 式を計算するのはREPLを使う
-- λΠ> double 2
-- 4 : Nat

-- 関数も値
-- λΠ> :printdef double
-- double : Nat -> Nat
-- double x = x + x

-- 関数式 `\引数... => 本体` で定義
double' : Nat -> Nat
double' = \x => x + x

-- λΠ> :printdef double'
-- double' : Nat -> Nat
-- double' = \x => x + x


-- 局所的な定義
quad : Nat -> Nat
quad x = let y = double x in 2 * y
-- λΠ> quad 2
-- 8 : Nat

-- 関数の入れ子
quad': Nat -> Nat
quad' x = double (double x)
-- λΠ> quad' 2
-- 8 : Nat


-- 局所的な関数定義。上書きもできる
triple: Nat -> Nat
triple x = double x + x
where
  double: Nat -> Nat
  double x = x + x
-- λΠ> triple 3
-- 9 : Nat


-- 整数とモジュール

-- 自然数の引き算は整数と違う
-- λΠ> 1 - 2
-- (input):1:3:When checking argument smaller to function Prelude.Nat.-:
--         Can't find a value of type 
--                 LTE 2 1


-- 整数を使ってみよう
namespace Z -- 定義の範囲を区切るために namespace を使う
  -- 名前空間内はインデントする

  -- 数値や演算子を整数として解釈する
  -- メモ: 整数の使い方が分からない
  --       ひとまず `the Integer` を付けると整数として計算してくれる
  -- λΠ> the Integer (1 - 2)
  -- -1 : Integer

  -- 割り算も使えるる '`div`' を使う。 '`' は関数を中置記法で呼ぶ構文
  -- λΠ> (2 + 3) `div` 2
  -- 2 : Integer

  -- 多引数の関数
  p : Integer -> Integer -> Integer
  p x y = 2 * x - y * y
  -- λΠ> :printdef p
  -- p : Integer -> Integer -> Integer
  -- p x y = fromInteger 2 * x - y * y
  -- λΠ> p 3 4
  -- -10 : Integer

  -- 関数式で
  p' : Integer -> Integer -> Integer
  p'  = \x, y => 2 * x - y * y
  -- λΠ> :printdef p'
  -- p' : Integer -> Integer -> Integer
  -- p' = \x, y => fromInteger 2 * x - y * y

  -- 部分適用
  q : Integer -> Integer
  q = p 3
  -- p と q の定義だけを展開する
  -- メモ: 部分的に定義を展開する方法が分からない

  -- λΠ> q 4
  -- -10 : Integer

  -- q の中の x の値は変わらない
  -- λΠ> let x = 0 in q x
  -- 6 : Integer

-- 名前空間が終わったらインデントを戻す

--
-- λΠ> :printdef Z.p
-- p : Integer -> Integer -> Integer
-- p x y = fromInteger 2 * x - y * y

-- Scope は元に戻る
-- メモ: そもそも名前空間内で整数演算をインポートしていないので戻るも何もない
-- λΠ> 1 - 2
-- (input):1:3:When checking argument smaller to function Prelude.Nat.-:
--         Can't find a value of type 
--                 LTE 2 1

-- 練習問題 2.1 Z の中で二つの整数値の平均を計算する関数 heikin : Z -> Z -> Z を定義せよ
-- メモ: Idrisのインターフェイス的に以下のheikinは全関数でない可能性がある
-- heikin : Integer -> Integer -> Integer
-- heikin x y = (x + y) `div` 2
-- λΠ> heikin 1 2
-- 1 : Integer
-- λΠ> heikin 8 2
-- 5 : Integer


-- データ型の定義

-- じゃんけんの手
data Janken = Gu | Choki | Pa

-- 弱点を返す
weakness : Janken -> Janken
-- 簡単な場合分け
weakness Gu = Pa
weakness Choki = Gu
weakness Pa = Choki
-- λΠ> weakness Pa
-- Choki : Janken


-- λΠ> :printdef Bool
-- data Bool : Type where
--   False : Bool
--   True : Bool

-- λΠ> :printdef Janken
-- data Janken : Type where
--   Gu : Janken
--   Choki : Janken
--   Pa : Janken

-- 「t1はt2に勝つ」という関係
wins : (t1 : Janken) -> (t2 : Janken) -> Bool
-- 2つの値で場合分け
wins Gu Choki = True
wins Choki Pa = True
wins Pa Gu = True
-- 残りは全部勝たない
wins _ _ = False

-- λΠ> wins
-- wins : Janken -> Janken -> Bool
-- 関係はboolへの他引数関数

-- λΠ> wins Gu Pa
-- False : Bool

-- 二人でゲームしよう
namespace Play2
  data Winner = First | Second | Aiko

  play : (t1 : Janken) -> (t2 : Janken) -> Winner
  play t1 t2 = if wins t1 t2 then First else
               if wins t2 t1 then Second else
               Aiko
  -- λΠ> play Gu Pa
  -- Second : Winner
  -- λΠ> play Choki Choki
  -- Aiko : Winner


-- λΠ> :printdef (&&)
-- (&&) : Bool -> Lazy Bool -> Bool
-- True && x = Force x
-- False && _ = False

-- λΠ> :printdef (||)
-- (||) : Bool -> Lazy Bool -> Bool
-- False || x = Force x
-- True || _ = True

namespace Play3

  data Winner = First | Second | Third | Aiko

  -- Idrisの名前空間はあまり賢くないのでPlay2のものを隠す必要がある
  %hide Play2.Winner

  play : (t1, t2, t3 : Janken) -> Winner
  play t1 t2 t3 = Aiko

  -- 練習問題 2.2 Play3.play を正しく定義せよ
  -- play : (t1 : Janken) -> (t2 : Janken) -> (t3 : Janken) -> Winner
  -- play t1 t2 t3 = if wins t1 t2 && wins t1 t3 then First else
  --                 if wins t2 t1 && wins t2 t3 then Second else
  --                 if wins t3 t1 && wins t3 t2 then Third else
  --                 Aiko



-- 再帰データ型と再帰関数
namespace MyNat -- Nat を新しく定義する
  % hide Prelude.Nat.Nat


  data Nat : Type where
    O : Nat
    S : Nat -> Nat


  -- plus : (m : MyNat.Nat) -> (n : MyNat.Nat) -> MyNat.Nat
  -- plus m n = case m of  -- 減らないとエラーになる
  --   O => n
  --   S m' => S (plus m n)
  -- - + Errors (1)
  --  `-- Idris1.idr line 235 col 2:
  --      Main.MyNat.plus is possibly not total due to recursive path Main.MyNat.plus --> Main.MyNat.plus


  -- 同じ型の引数をまとめる
  plus : (m, n : Nat) -> Nat
  plus O n = n
  plus (S m') n = S (plus m' n)
  -- λΠ> :printdef MyNat.plus
  -- plus : Nat -> Nat -> Nat
  -- plus O n = n
  -- plus (S m') n = S (plus m' n)

  -- 式の型を調べる
  -- λΠ> :t plus (S (S O)) (S O)
  -- plus (S (S O)) (S O) : Nat

  -- 式を評価する
  -- λΠ> plus (S (S O)) (S O)
  -- S (S (S O)) : Nat

  mult : (m, n : Nat) -> Nat
  mult m n = O
  -- λΠ> mult (S (S O)) (S O)
  -- S (S O) (* 期待している値 *) : Nat

  -- 練習問題 2.3 mult を正しく定義せよ．
  -- mult : (m, n : Nat) -> Nat
  -- mult O n = O
  -- mult (S m') n = plus (mult m' n) n
  -- λΠ> mult (S (S O)) (S O)
  -- S (S O) : Nat


-- 文字列の扱い
-- IdrisではデフォルトでPrelude.Stringが読み込まれている
s : String
s = "hello"
-- λΠ> :printdef s
-- s : String
-- s = "hello"

-- Idrisの文字列はデータ型ではない
-- λΠ> :printdef String
-- Not found
-- unpackなどを噛ませるとリストになる
-- λΠ> unpack "hello"
-- ['h', 'e', 'l', 'l', 'o'] : List Char


-- 文字列の結合
s2 : String
s2 = s ++ " " ++ "evelybody"
-- λΠ> s2
-- "hello evelybody" : String

-- 文字リテラル
-- λΠ> ' '
-- ' ' : Char

removeHeadSpace : String -> String
removeHeadSpace s = case unpack s of
  ' ' :: s' => pack s'
  _ => s

-- λΠ> removeHeadSpace " hello"
-- "hello" : String

removeHeadSpaces : (s : String) -> String
removeHeadSpaces s = ""
-- 先頭の空白を全て取る


-- 練習問題 2.4 remove head spaces を正しく定義せよ
-- removeHeadSpaces : (s : String) -> String
-- removeHeadSpaces s = pack (f (unpack s))
-- where
--   f : List Char -> List Char
--   f (' ' :: s') = f s'
--   f s'           = s'

-- λΠ> removeHeadSpaces "   hello"
-- "hello" : String
