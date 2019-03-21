[2018年度後期・数理解析・計算機数学 II (同 概論II)](https://www.math.nagoya-u.ac.jp/~garrigue/lecture/2018_AW/)をIdrisでやるメモ。

# ビルド
ビルドというか正しさのチェック。コンソールからは以下。

```console
$ idris --build Garrigue-lecture-2018_AW-in-Idris.ipkg
```

現実的にはEmacs(+REPL)などで正しさを検査しながら進める。型推論が通れば正しい。

# 参考

* [Coq勉強会](https://readcoqart.connpass.com/)
  + 本リポジトリはCoq勉強会の進行に合わせて進んでいく(予定)
* [PDFからCoqを抜き出したリポジトリ](https://github.com/nagaet/Garrigue-lecture-2018_AW)
  + 本リポジトリはこれをベースにすすめている
