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
      // location: [Tennessee, TN 59341],
      email: "leonardo.estacio.h@uni.pe",
      // url: "math.ue.edu/~jdoe"
    ),
  ),
  // abstract: lorem(100),
  // bibliography: bibliography("refs.bib"),
)

#show: great-theorems-init

#let mathcounter = rich-counter(
  identifier: "mathblocks",
  inherited_levels: 1
)

#let definition = mathblock(
    blocktitle: "Definition",
    counter: mathcounter
)

#let lemma = mathblock(
    blocktitle: "Lemma",
    counter: mathcounter
)

#let remark = mathblock(
  blocktitle: "Remark",
  prefix: [_Remark._],
  inset: 8pt,
  stroke: 0.2pt + black,
  // fill: lime,
  radius: 1pt,
)

#let proof = proofblock()

= Definite Integral

#lemma[
  Let $P = {x_0, x_1, ..., x_n} in P[a, b]$ and $c_1, c_2, ..., c_n in RR$ such
  that $x_(k-1) < c_k < x_k$
  - $inf(f) dot Delta x_k <= inf(f) dot (c_k - x_(k-1)) + inf(f) dot (x_k - c_k)$.
  - $sup(f) dot Delta x_k <= sup(f) dot (c_k - x_(k-1)) + sup(f) dot (x_k - c_k)$.
]

#lemma[
  Let $P, Q in P[a, b]$. If $P subset Q$ then
  - $L(f, P) <= L(f, Q)$.
  - $U(f, P) >= U(f, Q)$.
]
#proof[
  Let $P = {x_0, x_1, ..., x_n}$ suppose for $Q$ the following $
      a = x_0 < c_1 < x_1 < c_2 < x_2 < ... < x_(n-1) < c_n < x_n = b.
  $ For each $k in I_n$ we have $
      inf(f) dot Delta x_k <= inf(f) dot (c_k - x_(k-1)) + inf(f) dot (x_k - c_k)
  $ then $
      sum _(k=1)^n inf(f) dot Delta x_k <=
      sum _(k=1)^n inf(f) dot (c_k - x_(k-1)) +
      sum _(k=1)^n inf(f) dot (x_k - c_k) \
      L(f, P) <= L(f, Q).
  $
]

#remark[
  In a refinement of a partition, the lower sum is #underline[crescent]
  and the upper sum is #underline[decrescent].
]

#remark[
  The following $
      L(f, P) <= M dot (b - a), quad forall P in P[a, b]
  $ implies ${L(f, P) | P in P[a, b]}$ is a set with an upper bound.
  Therefore it has a supremum.
]

#remark[
  The following $
      m dot (b - a) <= U(f, P), quad forall P in P[a, b]
  $ implies ${U(f, P) | P in P[a,b]}$ is a set with a lower bound.
  Therefore it has an infimum.
]

#definition[
  The lower integral of a function $f$ is defined as $
    underline(integral _a^b) f = sup L(f, P), quad P in P[a, b].
  $
]

#definition[
  The upper integral of a function $f$ is defined as $
    overline(integral _a^b) f = inf U(f, P), quad P in P[a, b].
  $
]

#lemma[
  $forall P, Q in P[a,b]: L(f, P) <= U(f, Q)$.
]
#proof[
  Let $P, Q in P[a,b]$ we know $P union Q in P[a,b]$, then $
      P subset (P union Q) => L(f, P) <= L(f, P union Q) \
      Q subset (P union Q) => U(f, P union Q) <= U(f, Q)
  $ where $
      L(f, P) <= L(f, P union Q) <= U(f, P union Q) <= U(f, Q)
  $ therefore $
      L(f, P) <= U(f, Q), quad forall P, Q in P[a, b].
  $
]

#lemma[
  $ underline(integral _a^b) f <= overline(integral _a^b) f $
]
#proof[
  Let $Q in P[a,b]$ then $
      L(f, P) & <= U(f, Q), quad forall P in P[a, b]. 
  $ evaluate the supremum on both sides $
      sup L(f, P) &<= sup U(f, Q) \
      underline(integral _a^b) f & <= U(f, Q)
  $ evaluate the infimum on both sides $
      inf underline(integral _a^b) f & <= inf U(f, Q) \
      underline(integral _a^b) f & <= overline(integral _a^b) f
  $
]

#definition[
  Let $a, b in RR$ with $a < b$ and $f: [a, b] -> RR$ a bounded
  function. The function $f$ is said to be Riemann integrable if
  and only if $
      underline(integral _a^b) f = overline(integral _a^b) f
  $ in this case, the definite integral of $f$ over the interval
  $[a,b]$ is $
      integral _a^b f = underline(integral _a^b) f = overline(integral _a^b) f.
  $
]

#lemma[
  Let $a, b in RR$ with $a < b$ and $f: [a, b] -> RR$ an integrable
  function. Then, given $epsilon > 0$,
  $
    exists P_1, P_2 in P[a, b] :
    integral _a^b f - epsilon < L(f, P_1) <= integral _a^b f <= U(f, P_2) <
    integral _a^b f + epsilon.
  $
]
#proof[
  The function $f$ is integrable over $[a,b]$, therefore $
      integral _a^b f = underline(integral _a^b) f = overline(integral _a^b) f.
  $ and $
      integral _a^b f = underline(integral _a^b) f = sup{L(f, P_1) | P_1 in P[a, b]}
  $ then $
      forall epsilon > 0 : exists P_1 in P[a, b] " such that "
      integral _a^b f - epsilon < I(f, P_1) <= integral _a^b f.
  $ Furthermore $
      integral _a^b f = overline(integral _a^b) f = inf{U(f, P_2) | P_2 in P[a, b]}
  $ then $
      forall epsilon > 0 : exists P_2 in P[a,b] " such that "
      integral _a^b f <= I(f, P_1) < integral _a^b f + epsilon.
  $ Therefore $
      integral _a^b f - epsilon < L(f, P_1) <= integral _a^b f <= U(f, P_2) <
      integral _a^b f + epsilon.
  $
]

#lemma[
  Let $a, b in RR$ with $a < b$ and $f: [a, b] -> RR$ an integrable
  function. Then, given $epsilon > 0$,
  $
    exists P in P[a, b] :
    integral _a^b f - epsilon < L(f, P) <= integral _a^b f <= U(f, P) <
    integral _a^b f + epsilon.
  $
]

#lemma[
  Let $a, b in RR$ with $a < b$ and $f: [a, b] -> RR$ an integrable
  function in $[a, b]$. Then, given $epsilon > 0$,
  $
    exists P in P[a, b] : U(f, P) - L(f, P) < epsilon.
  $
]<lem>

#lemma[
  Let $a in RR$. If $forall epsilon > 0: 0 <= a < epsilon$ then $a = 0$.
]

#lemma[
  Let $a, b in RR$ with $a < b$ and $f: [a, b] -> RR$ a bounded function
  function in $[a, b]$. If @lem holds for a given $epsilon > 0$, then $f$
  is Riemann integrable in $[a, b]$.
]
#proof[
  Given $epsilon > 0$, @lem holds, $
      L(f, P) <= underline(integral _a^b) f <= overline(integral _a^b) f <= U(f, P),
  $ then $
      overline(integral _a^b) - underline(integral _a^b) f <= U(f, P) - L(f, P) < epsilon.
  $ For any given $epsilon > 0 $,
  $
      0 <= overline(integral _a^b) - underline(integral _a^b) < epsilon =>
      overline(integral _a^b) = underline(integral _a^b).
  $
]

#lemma[
  Let $a, b in RR$ with $a < b$ and $f: [a, b] -> RR$ a bounded
  function. The following is equivalent.
  - $f$ is Riemann integrable in $[a, b]$.
  - Given $epsilon > 0$, @lem holds.
]

#lemma[
  Let $a, b in RR$ with $a < b$ and $f: [a, b] -> RR$ a bounded
  function $
      L(f, P) <= sum _(k=1)^n f(overline(x)_k) dot Delta x_k <= U(f, P),
      quad overline(x)_k in [x_(k-1), x_k].
  $ If $f$ is integrable, then $
      abs(integral _a^b f - sum _(k=1)^n f(overline(x)_k) dot Delta x_k) <= U(f, P)
      - L(f, P).
  $
]
#proof[
  Let $P in P[a, b]$
  $
      m_k <= f(overline(x)_k) <= M_k, quad forall k = 0, 1, 2, ..., n.
  $ $Delta x_k > 0$,
  $
      m_k dot Delta x_k <= f(overline(x)_k) dot Delta x_k <= M_k dot Delta x_k
  $ then, $
        sum _(k=1)^n m_k              dot Delta x_k <=
      & sum _(k=1)^n f(overline(x)_k) dot Delta x_k <=
        sum _(k=1)^n M_k              dot Delta x_k \
      L(f, P) <= & sum _(k=1)^n f(overline(x)_k) dot Delta x_k <= U(f, P).
  $
  #remark[
    If $f$ is integrable, then $
      L(f, P) <= integral _a^b f <= U(f, P).
    $
  ]
  Therefore $
      L(f, P) - U(f, P) <=
          integral _a^b f - sum _(k=1)^n f(overline(x)_k) dot Delta x_k  <=
      U(f, P) - L(f, P) \
      abs(integral _a^b f - sum _(k=1)^n f(overline(x)_k) dot Delta x_k) <=
      U(f, P) - L(f, P).
  $
]
