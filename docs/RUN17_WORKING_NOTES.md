# Run17 — 原稿へ戻す証明上の短縮

SCの一意性補題は、原典のprogression/coset分類を経由しない。
prefixの位置付き部分列和集合をS (空和0を含む) とする。
bを付けて零和自由性を保ち、和集合のcardが1だけ増えるなら、
平行移動は同じcardで0を含まないため

`S.erase 0 ⊆ b+S`。

二つの候補b,cについて、prefixが非空ならc∈Sである。
cが唯一の新しい和ならprefix総和が0になるためである。
c≠0からc−b∈S、b≠cならさらに(c−b)−c=−b∈Sとなる。
これはbを付けた列の零和自由性に反する。従ってb=c。
対応する実証明は`erase_zero_subset_translate`・`Sharp.backward`・`sharp_term_unique`。

末尾の候補を比較するときも、sharpならprefixの和集合は
「全和集合から列の総和だけを除いたもの」であり、同じSになる。
`sharp_terminal_unique`はこの事実から導く。

以後はLevのconnected方針を、順列を明示的に構成する代わりに元の位置集合の導出木で実装。
各挿入の値が既存subset sumsの差に入ることを保存し、
零和自由性から正係数と総和<addOrderOfを帰納的に得る。
最後のlong条件と位数の整除でその位数がuと一致し、逆unitがSCの実証人になる。

この短縮はSCの結論を仮定しない。元の一般SC命題は凍結型のまま証明される。
actual sourceのunit変換やR/Hx不変性を意味するものではない。
