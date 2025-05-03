#import "@preview/unequivocal-ams:0.1.2": ams-article
#import "@preview/great-theorems:0.1.2": *
#import "@preview/rich-counters:0.2.1": *

#show: ams-article.with(
  title: [Integral Calculus],
  authors: (
    (
      name: "Leonardo Estacio",
      department: [Faculty of Science],
      organization: [National University of Engineering],
      email: "leonardo.estacio.h@uni.pe",
    ),
  ),
)

#show: great-theorems-init

#let mathcounter = rich-counter(
  identifier: "mathblocks",
  inherited_levels: 1
)

#let mathcounter_def = rich-counter(
  identifier: "mathblocks_def",
  inherited_levels: 1
)

#let definition = mathblock(
    blocktitle: "Definition",
    counter: mathcounter_def
)

#let lemma = mathblock(
    blocktitle: "Lemma",
    counter: mathcounter
)

#let theorem = mathblock(
    blocktitle: "Theorem",
    counter: mathcounter
)

#let proposition = mathblock(
    blocktitle: "Proposition",
    counter: mathcounter
)

#let corollary = mathblock(
    blocktitle: "Corollary",
    counter: mathcounter
)

#let remark = mathblock(
  blocktitle: "Remark",
  prefix: [_Remark._],
  inset: 8pt,
  stroke: 0.2pt + black,
  fill: luma(230),
  radius: 1pt,
)

#let claim = mathblock(
  blocktitle: "Claim",
  prefix: [_Claim._],
  inset: 8pt,
  stroke: 0.2pt + black,
  fill: luma(230),
  radius: 1pt,
)

#let proof = proofblock()

= Definite Integral

#lemma[
  Let $P = {x_0, x_1, ..., x_n} in cal(P)[a, b]$ and $c_1, c_2, ..., c_n in RR$ such
  that $x_(k-1) < c_k < x_k$
  - $inf f dot Delta x_k <= inf f dot (c_k - x_(k-1)) + inf f dot (x_k - c_k)$.
  - $sup f dot Delta x_k >= sup f dot (c_k - x_(k-1)) + sup f dot (x_k - c_k)$.
]

#lemma[
  Let $P, Q in cal(P)[a, b]$. If $P subset Q$ then
  - $L(f, P) <= L(f, Q)$.
  - $U(f, P) >= U(f, Q)$.
]
#proof[
  Let $P = {x_0, x_1, ..., x_n}$ and suppose for $Q$ the following $
      a = x_0 < c_1 < x_1 < c_2 < x_2 < ... < x_(n-1) < c_n < x_n = b.
  $ For each $k in I_n$ we have $
      inf f dot Delta x_k <= inf f dot (c_k - x_(k-1)) + inf f dot (x_k - c_k),
  $ then $
      sum _(k=1)^n inf f dot Delta x_k <=
      sum _(k=1)^n inf f dot (c_k - x_(k-1)) +
      sum _(k=1)^n inf f dot (x_k - c_k) \
      L(f, P) <= L(f, Q).
  $
]

#remark[
  In a refinement of a partition, the lower sum is #underline[crescent]
  and the upper sum is #underline[decrescent].
]

#remark[
  The following $
      L(f, P) <= M dot (b - a), quad forall P in cal(P)[a, b]
  $ implies ${L(f, P) : P in cal(P)[a, b]}$ is a set with an upper bound.
  Thus it has a supremum.
]

#remark[
  The following $
      m dot (b - a) <= U(f, P), quad forall P in cal(P)[a, b]
  $ implies ${U(f, P) : P in cal(P)[a,b]}$ is a set with a lower bound.
  Thus it has an infimum.
]

#pagebreak()

#definition[
  The lower integral of a function $f$ is defined as $
    underline(integral _a^b) f := sup{L(f, P) : P in cal(P)[a, b]}.
  $
]

#definition[
  The upper integral of a function $f$ is defined as $
    overline(integral _a^b) f := inf{U(f, P) : P in cal(P)[a,b]}.
  $
]

#lemma[
  $forall P, Q in cal(P)[a,b]: L(f, P) <= U(f, Q)$.
]<lemmi>

#proof[
  Let $P, Q in cal(P)[a,b]$ and $P union Q in cal(P)[a,b]$ then $
    #block[
      $
        P subset (P union Q) &=> L(f, P) <= L(f, P union Q) \
        Q subset (P union Q) &=> U(f, P union Q) <= U(f, Q)
      $
    ],
  $ hence $
      L(f, P) <= L(f, P union Q) <= U(f, P union Q) <= U(f, Q).
  $ Therfore $
      L(f, P) <= U(f, Q), quad forall P, Q in cal(P)[a, b].
  $
]

#lemma[
  Let $a, b in RR$ with $a < b$ and $f: [a, b] -> RR$ a bounded function
  function such that $m <= f(x) <= M, forall x in [a, b]$, then
  $
      m (b - a) <= underline(integral _a^b) f <=
                    overline(integral _a^b) f <= M (b - a).
  $
]
#remark[
  $
    forall P in cal(P)[a, b] :
    m (b - a) <= L(f, P) <= U(f, p) <= M (b - a).
  $
]
#proof[
  By definition, the lower integral is the supremum of the lower sum, thus $
      m (b - a) <= L(f, P) <= underline(integral _a^b) f =>
      m (b - a) <= underline(integral _a^b) f.
  $ Likewise, for the upper integral, by definition; the upper integral is the infimum
    of the upper sum, thus $
      overline(integral _a^b) f <= U(f, P) <= M (b - a) =>
      overline(integral _a^b) f <= M (b - a).
  $ From @lemmi we have $
      forall P, Q in cal(P)[a, b]: L(f, P) <= U(f, Q).
  $ By definition of the lower integral, $
      forall    Q in cal(P)[a, b]: underline(integral _a^b) f <= U(f, Q),
  $ again, by definition of the upper integral, $
      underline(integral _a^b) f <= overline(integral _a^b) f.
  $ Thus, $
      m (b - a) <= underline(integral _a^b) f <=
                    overline(integral _a^b) f <= M (b - a).
  $
]

#lemma[
  Let $a, b in RR$ with $a < b$ and $f: [a, b] -> RR$ an integrable
  function. Then, given $epsilon > 0$, exists $P_1, P_2 in cal(P)[a, b]$
  such that $
      integral _a^b f - epsilon < L(f, P_1) <= integral _a^b f <= U(f, P_2) <
      integral _a^b f + epsilon.
  $
]<lemm>
#remark[
  $
    integral _a^b f = underline(integral _a^b) f = sup{L(f, P_1) : P_1 in cal(P)[a, b]}.
  $
]
#remark[
  $
    integral _a^b f = overline(integral _a^b) f = inf{U(f, P_2) : P_2 in cal(P)[a, b]}.
  $
]
#proof(of: <lemm>)[
  The function $f$ is integrable over $[a,b]$, hence $
      integral _a^b f = underline(integral _a^b) f = overline(integral _a^b) f.
  $
  For all $epsilon > 0$, exists $P_1 in cal(P)[a, b]$ such that $
      integral _a^b f - epsilon < L(f, P_1) <= integral _a^b f.
  $
  For all $epsilon > 0$, exists $P_2 in cal(P)[a,b]$ such that $
      integral _a^b f <= U(f, P_2) < integral _a^b f + epsilon.
  $ Thus, $
      integral _a^b f - epsilon < L(f, P_1) <= integral _a^b f <= U(f, P_2) <
      integral _a^b f + epsilon.
  $
]

#lemma[
  Let $a, b in RR$ with $a < b$ and $f: [a, b] -> RR$ an integrable
  function. Then, given $epsilon > 0$, exists $P in cal(P)[a, b]$
  such that $
      integral _a^b f - epsilon < L(f, P) <= integral _a^b f <= U(f, P) <
      integral _a^b f + epsilon.
  $
]

#lemma[
  Let $a, b in RR$ with $a < b$ and $f: [a, b] -> RR$ an integrable
  function in $[a, b]$. Then, given $epsilon > 0$, exists $P in
  cal(P)[a, b]$ such that $
      U(f, P) - L(f, P) < epsilon.
  $
]<lem>

#lemma[
  Let $a, b in RR$ with $a < b$ and $f: [a, b] -> RR$ a bounded function
  function in $[a, b]$. If @lem holds for any $epsilon > 0$, then $f$
  is Riemann integrable in $[a, b]$.
]<lem_ep>
#remark[
  Let $a in RR$. If $forall epsilon > 0: 0 <= a < epsilon$ then $a = 0$.
]
#remark[
  $
    L(f, P) <= underline(integral _a^b) f <= overline(integral _a^b) f
    <= U(f, P), quad P in cal(P)[a, b]
  $
]
#proof(of: <lem_ep>)[
  Suppose $forall epsilon > 0$, @lem holds, then $
      overline(integral _a^b) - underline(integral _a^b) f <= U(f, P) - L(f, P) < epsilon.
  $ Hence, $
      0 <= overline(integral _a^b) - underline(integral _a^b) < epsilon =>
      overline(integral _a^b) = underline(integral _a^b).
  $
]
#remark[
  If the function $f$ is Riemann integrable, then @lem holds.
]

#lemma[
  Let $a, b in RR$ with $a < b$ and $f: [a, b] -> RR$ a bounded
  function, for some $P in cal(P)[a, b]$, we have
  $
      L(f, P) <= sum _(k=1)^n f(overline(x)_k) dot Delta x_k <= U(f, P),
      quad overline(x)_k in [x_(k-1), x_k].
  $
]<lem_ll>
#proof[
  Let $P in cal(P)[a, b]$, we have
  $
      m_k (f) <= f(overline(x)_k) <= M_k (f), quad forall k in I_n.
  $ Since $Delta x_k > 0$,
  $
      m_k (f) dot Delta x_k <= f(overline(x)_k) dot Delta x_k <=
      M_k (f) dot Delta x_k,
  $ then, $
        sum _(k=1)^n m_k (f)          dot Delta x_k <=
      & sum _(k=1)^n f(overline(x)_k) dot Delta x_k <=
        sum _(k=1)^n M_k (f)          dot Delta x_k \
      L(f, P) <= & sum _(k=1)^n f(overline(x)_k) dot Delta x_k <= U(f, P).
  $
]

#lemma[
  Let $a, b in RR$ with $a < b$ and $f: [a, b] -> RR$ a bounded and integrable
  function, for some $P in cal(P)[a, b]$, we have $
      abs(integral _a^b f - sum _(k=1)^n f(overline(x)_k) dot Delta x_k) <=
      U(f, P) - L(f, P).
  $
]<lem_l>
#remark[
  If $f$ is integrable, then $
    L(f, P) <= integral _a^b f <= U(f, P).
  $
]
#proof(of: <lem_l>)[
  From @lem_ll, we have $
      L(f, P) <= sum _(k=1)^n f(overline(x)_k) dot Delta x_k <= U(f, P),
      quad overline(x)_k in [x_(k-1), x_k].
  $ Then, $
      L(f, P) - U(f, P) <=
          integral _a^b f - sum _(k=1)^n f(overline(x)_k) dot Delta x_k  <=
      U(f, P) - L(f, P) \
      abs(integral _a^b f - sum _(k=1)^n f(overline(x)_k) dot Delta x_k) <=
      U(f, P) - L(f, P).
  $
]

#pagebreak()

#proposition[
  If $f$ is a nondecreasing function over $[a, b]$, then $f$ is integrable over
  $[a, b]$.
]

#proof[
  Let $P in cal(P)[a, b]$.
  $
    U(f, P) - L(f, P) &= sum _(k=1)^n [f(x_k) - f(x_(k-1))] Delta x_k \
    &<= ||P|| sum _(k=1)^n [f(x_k) - f(x_(k-1))] \
    &<= ||P||[f(b) - f(a)], quad forall P in cal(P)[a, b].
  $
  For any given $epsilon > 0$ define $||P|| = epsilon / (f(b) - f(a))$, therefore
  $
      U(f, P) - L(f, P) < epsilon.
  $
  From @lem, $f$ is an integrable function.
]

#proposition[
  Let $f$ be a differentiable over $[a, b]$ and $|f'(x)| <= k, forall x
  in [a, b]$. From the MVT
  + $forall P in cal(P)[a, b]: U(f, P) - L(f, P) <= k||P||(b - a)$.
  + $f$ is integrable over $[a, b]$.
  + $
        abs(integral _a ^b f(x) dif x - 1/2 (U(f, P) + L(f, P))) <= 1/2 k||P||(b - a).
    $
]
