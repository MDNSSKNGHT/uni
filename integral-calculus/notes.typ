#import "@preview/unequivocal-ams:0.1.2": ams-article
#import "@preview/cetz:0.3.4": canvas, draw
#import "@preview/cetz-plot:0.1.1": plot, chart
#import "@preview/lemmify:0.1.8": *
#import "@preview/delimitizer:0.1.0": *

#show: ams-article.with(
  title: [Notes on Integral Calculus],
  authors: (
    (
      name: "Leonardo Estacio",
      department: [Faculty of Science],
      organization: [National University of Engineering],
      // location: [Columbia, SC 29208],
      // email: "howard@math.sc.edu",
      // url: "www.math.sc.edu/~howard"
    ),
  ),
  abstract: lorem(100),
)

#let(
  theorem, lemma, corollary,
  remark, proposition, example,
  proof, rules: thm-rules
) = default-theorems("thm-group", lang: "en")
#show: thm-rules

#let sup = math.op("sup", limits: true)
#let inf = math.op("inf", limits: true)

= Definite integral

= Area

Let $f: [a, b] -> RR$ such that $f(x) >= 0, forall x in [a, b]$. Let us define
$
    R = { (x, y) : x in [a, b] and y in [0, f(x)] }
$
as the area under $f$ from $a$ to $b$.

#align(center)[
  #canvas({
    import draw: *

    set-style(stroke: 0.5pt)

    plot.plot(
      name: "plot",
      size: (4, 4), 
      x-tick-step: none,
      y-tick-step: none,
      axis-style: "school-book",
      {
        plot.add(domain: (0, 8), x => calc.pow(1.5, x) + 2)
        plot.add(domain: (2, 7), x => 0)

        plot.add-fill-between(
          domain: (2, 7),
          x => calc.pow(1.5, x) + 2,
          x => 0
        )

        plot.add-anchor("point-a", (2, -1.5))
        plot.add-anchor("point-b", (7, -1.5))
      }
    )

    content("plot.point-a", [x = a])
    content("plot.point-b", [x = b])
  })
]

The area is denoted as $A_a^b (f)$. The following properties hold for bounded,
non-negative functions
+ If $f(x) <= g(x), forall x in [a, b]$ then $A_a^b (f) <= A_a^b (g)$.
+ $A_a^b (f) = A_a^c (f) + A_c^b (f), forall c in [a, b]$.
+ $A_a^b (C) = C(b - a), C >= 0$.

#theorem[
  The area under a function within some closed interval can be calculated as the
  definite integral of said function in the given interval. That is,
  $
      A_a^b (f) = integral_a^b f. 
  $
]

#proof[
  Let $P = {x_0, x_1, ..., x_n}$ a partition of $[a, b]$ such that
  $
      m_k (f) Delta x_k <= A_(x_(k - 1))^(x_k) (f) <= M_k (f) Delta x_k,
        quad forall k in 1, 2, ..., n.
  $
  Then, 
  $
      sum_(k=1)^n m_k (f) Delta x_k <= sum_(k=1)^n A_(x_(k - 1))^(x_k) (f)
        <= sum_(k=1)^n M_k (f) Delta x_k.
  $
  Likewise,
  $
      L(f, P) <= A_a^b (f) <= U(f, P).
  $
  Moreover, $A_a^b (f)$ is an upper bound of ${ L(f, P) : P in cal(P)[a, b] }$
  and a lower bound of ${ U(f, P) : P in cal(P)[a, b] }$. Hence,
  $
      underline(integral_a^b) <= A_a^b (f) <= overline(integral_a^b).
  $
  Therefore, for integrable functions,
  $
      A_a^b (f) = integral_a^b f. 
  $
]

#theorem[
  Every continuous function within a given interval is also integrable in the
  same interval.
]<continuity_to_integrability>

#proof[
  Assume the function $f$ is continuous in $[a, b]$. By definition, for any given
  $epsilon > 0, exists delta$ such that $x, y in [a, b]$ and $abs(x - y) < delta$,
  then $abs(f(x) - f(y)) < e / (y - x)$.

  Let $P$ be a partition of $[a, b]$ such that $abs(x - y) < delta$,
  $
      U(f, P) - L(f, P) &= sum_(k=1)^n ( sup_([x_(k - 1), x_k]) f -
        inf_([x_(k - 1), x_k]) f ) Delta x_k \
      &<= epsilon / (y - x) (y - x) = epsilon.
  $
  Therefore, $f$ is integrable over $[a, b]$.
]

#theorem[
  If $f$ is a continuous function in $[a, b]$, then for every $epsilon > 0, exists
  delta > 0$ such that
  $
      abs(integral_a^b - sum_(k=1)^n f(overline(x)_k) Delta x_k) < epsilon.
  $
  For any partition $P$ with $norm(P) < delta$ and for every $overline(x)_k in
  [x_(k - 1), x_k]$.
]

#proof[
  Let $P$ be a partition of $[a, b]$ and $overline(x) in [x_(k - 1), x_k]$,
  $
      L(f, P) <= sum_(k=1)^n f(overline(x)) Delta x_k <= U(f, P).
  $
  Now then; if $f$ is continuous in $[a, b]$, by @continuity_to_integrability, $f$ is
  integrable over $[a, b]$. Thus,
  $
      L(f, P) <= integral_a^b f <= U(f, P).
  $
  Therefore
  $
      L(f, P) - U(f, p) <= integral_a^b f - sum_(k=1)^n f(overline(x)) Delta x_k
        <= U(f, P) - L(f, P).
  $
  Likewise
  $
      0 <= abs(integral_a^b f - sum_(k=1)^n f(overline(x)) Delta x_k) <= U(f, P)
        - L(f, P).
  $
  Given $epsilon > 0, exists delta > 0$ such that $x, y in [a, b]$ and $abs(x - y)
  => abs(f(x) - f(y)) < epsilon / (b - a)$. From where $norm(P) < delta$, implies
  $
      U(f, P) - L(f, P) < sum_(k=1)^n epsilon / (b - a) (x_k - x_(k - 1)) = epsilon.
  $
]

#corollary[
  If $f$ is continuous in $[a, b]$, then
  $
    integral_a^b f = lim_(norm(P) -> 0) sum_(k=1)^n f(overline(x)_k) Delta x_k
  $
  where $overline(x)_k in [x_(k - 1), x_k]$ and for all $P in cal(P)[a, b]$.
]

== Approximation Error of an Integral

From
$
    L(f, P) <= integral_a^b f <= U(f, P),
$
we can take $1/2 (U(f, P) - L(f, P))$ as an upper bound of the approximation error
of the partition $P$ when taking $1/2 (U(f, P) + L(f, P))$ as the
value for the definite integral. That is,
$
    abs(integral_a^b f - 1/2 (U(f, P) + L(f, P))) <= 1/2 (U(f, P) - L(f, P)).
$

== The Integral as the Limit of the Sums

Let $f$ a bounded function in $[a, b]$ and $overline(x) in [x_(k - 1), x_k]$ such
that
$
    Delta x_k = (b - a) / n, quad x_k = a + k Delta x_k = a + k(b - a) / n, quad
      k = 1, ..., n
$
Hence, $f$ is integrable in $[a, b]$ and can be expressed as
$
    integral_a^b f = lim_(n -> oo) sum_(k=1)^n f(overline(x)) Delta x_k.
$

#example[
  Rewrite the following limit as a definite integral
  $
    lim_(norm(P) -> 0) sum_(k=1)^n sqrt((x_k - x_(k-1))^2 + (cos(x_k) - cos(x_(k-1)))^2),
  $
  over $[0, pi]$.

  Let $a = 0$ and $b = pi$. Then
  $
    sqrt((x_k - x_(k-1))^2 + (cos(x_k) - cos(x_(k-1)))^2) = abs(x_k - x_(k-1)) sqrt(1
      + (frac(cos(x_k) - cos(x_(k-1)), x_k - x_(k-1)))^2)
  $
  From MVT, $cos(x_k) - cos(x_(k-1)) = (-sin(overline(x)_k))(x_k - x_(k-1))$
  $
    sqrt((x_k - x_(k-1))^2 + (cos(x_k) - cos(x_(k-1)))^2) = abs(Delta x_k) sqrt(1
      + sin^2(overline(x)_k)).
  $
  For $overline(x)_k in [x_(k-1), x_k]$ hence $f(x) = sqrt(1 + sin^2(x))$. Therefore
  $
    lim_(norm(P) -> 0) sum_(k=1)^n sqrt((x_k - x_(k-1))^2 + (cos(x_k) - cos(x_(k-1)))^2)
      = integral_0^pi sqrt(1 + sin^2(x)) d x.
  $
]

== Basic Properties of the Integral

+ $ integral_a^b C d x = C (b - a). $
+ If $f$ is integrable over $[A, B]$ and $[a, b] subset [A, B]$, then $f$ is integrable
  over $[a, b]$.
+ If $f$ is bounded in $[a, b]$ and $c in [a, b]$, then
  $
      underline(integral_a^b) f = underline(integral_a^c) f + underline(integral_c^b) f
        and overline(integral_a^b) f = overline(integral_a^c) f + overline(integral_c^b) f.
  $
+ If $f$ and $g$ are bounded in $[a, b]$, then
  $
      underline(integral_a^b) f + underline(integral_a^b) g <= underline(integral_a^b) (f + g)
        and overline(integral_a^b) (f + g) <= overline(integral_a^b) f + overline(integral_a^b) g.
  $
+ If $c in [a, b]$ and $f$ is integrable in $[a, b]$, then $f$ is integrable in $[a, c]$
  and $[c, b]$ and
  $
      integral_a^b f = integral_a^c f + integral_c^b f.
  $
+ If $c in [a, b]$ and $f$ is integrable in $[a, c]$ and in $[c, b]$ then $f$ is integrable in
  $[a, b]$ and 
  $
      integral_a^c f + integral_c^b f = integral_a^b f.
  $
+ If $f$ is integrable in $[a, b]$ then $c f$ is integrable in [a, b] for any constant $c$. That
  is,
  $
      integral_a^b c f = c integral_a^b f.
  $
+ If $f$ and $g$ are integrable in $[a, b]$ then $(f + g)$ is integrable in $[a, b]$. That is,
  $
      integral_a^b (f + g) = integral_a^b f + integral_a^b g.
  $
+ If $f$ and $g$ are integrable in $[a, b]$ and $f(x) <= g(x), forall x in [a, b]$ then
  $
      integral_a^b f <= integral_a^b g.
  $
+ If $f$ is integrable in $[a, b]$, then $abs(f)$ is integrable in $[a, b]$ and
  $
      abs(integral_a^b f) = integral_a^b abs(f).
  $
+ If $f$ is integrable in $[A, B]$ and if $A <= b <= a <= B$, then
  $
      integral_b^a f = - integral_a^b f.
  $

== The Fundamental Theorem of Calculus

Let $G$ be a function defined by
$
    G(x) = integral_a^x f(t) d t
$
If $f$ is continuous on a given interval $I$ and $a in I$, then $G$ is differentiable on $I$
and $G'$ is an antiderivative of $f$ on $I$.

#proof[
  Let $x_0, x_0 + h in [a, b]$. From the definition of $G$
  $
      G(x_0 + h) - G(x_0) = integral_a^(x_0 + h) f(t) d t - integral_a^x_0 f(t) d t
        = integral_(x_0)^(x_0 + h) f(t) d t.
  $
  Therefore, for $h != 0$
  $
      (G(x_0 + h) - G(x_0)) / h = 1/h integral_(x_0)^(x_0 + h) f(t) d t,
  $
  note that $f(x_0) = 1/h integral_(x_0)^(x_0 + h) f(x_0) d t$. Then
  $
      (G(x_0 + h) - G(x_0)) / h - f(x_0) = 1/h integral_(x_0)^(x_0 + h) [f(t) - f(x_0)] d t.
  $
  Note further that $f$ is continuous, hence it is continuous in $x_0$; $forall epsilon > 0,
  exists delta > 0 slash forall t in I inter (x_0 - h, x_0 + h) => abs(f(t) - f(x_0)) <
  epsilon$. Therefore, for $0 < h < delta$ and $x_0 + h in I => abs(f(t) - f(x_0)) < epsilon$
  if and only if $x_0 <= t <= x_0 + h$ if $h > 0$ or $x_0 + h <= t <= x_0$ if $h < 0$. Thus,
  for $abs(h) < delta$ and $x_0 + h in I$,
  $
      abs((G(x_0 + h) - G(x_0)) / h - f(x_0)) < abs(1/h integral_(x_0)^(x_0 + h) epsilon d t)
        = epsilon.
  $
  Likewise
  $
      G'(x_0) = lim_(h -> 0) (G(x_0 + h) - G(x_0)) / h = f(x_0), forall x_0 in I.
  $
]

#corollary[
  Let $f$ be a continuous function on $RR$ and let $g$ and $h$ be differentiable functions on
  $RR$. Then,
  $
      D_x integral_h(x)^g(x) f(t) d t = f(g(x)) g'(x) - f(h(x)) h'(x), quad x in RR.
  $
]

#corollary[
  If $f$ is continuous on $RR$ and $g$ is differentiable on $RR$ with $g'$ continuous on $RR$,
  then
  $
      integral_a^x f(g(t)) g'(t) d t = integral_g(a)^g(x) f(u) d u, quad x in RR.
  $
]

#corollary[
  Let $f$ be an odd function (or even function) such that $f$ is continuous on $[-a, a]$ and let
  $
      g(x) = integral_0^x f(t) d t, forall x in [-a, a].
  $
  Then, g is an even function (or odd function). 
]

#corollary[
  Let $f$ be a continuous function on $[a, b]$ and $c in [a, b]$. Then,
  $
      lim_(h -> 0) 1/h integral_c^(c+h) f(t) d t = f(c).
  $
]

#theorem(name: "Newton-Leibniz theorem")[
  Let $f$ be a continuous function on $I$. If $F$ is differentiable on $I$ and $F' = f$ on $I$,
  then for any $[a, b] subset I$,
  $
      integral_a^b f(t) d t = F(b) - F(a).
  $
]

#proof[
  Let
  $
      G(x) = integral_a^x f(t) d t.
  $
  By the FTC, $G' = f$ on $I$. Therefore $G' = F'$ on $I$ and
  $
      G(x) = integral_a^x f(t) d t = F(x) + C.
  $
  For any given constant $C$ and $forall x in I$. For $x = a => G(a) = 0$. Likewise
  $
      G(a) = 0 = F(a) + C => C = -F(a).
  $
  Thus
  $
      G(b) = integral_a^b f(t) d t = F(b) - F(a).
  $
]

== Mean Value Theorem for Integrals

Let $f$ be an integrable function in $[a, b]$. The mean of $f$ on $[a, b]$ is defined
as
$
    overline(f) := 1 / (b - a) integral_a^b f.
$

#theorem[
  If $f$ is continuous on $[a, b]$ then $exists c in (a, b)$ such that $f(c)
  = overline(f)$. That is,
  $
      integral_a^b f = f(c) dot (b - a).
  $
]

#proof[
  Let $
    G(x) = integral_a^x f(t) d t, forall x in [a, b].
  $
  From the FTC, $G$ is differentiable on $[a, b]$. Let us apply the MVT to $G$. Therefore,
  $exists in (a, b) slash G(b) - G(a) = G'(c) (b - a)$. Likewise,
  $
      integral_a^b f(t) d t = f(c) dot (b - a).
  $
]

#theorem(name: "Weighted MVT for Integrals")[
  If $f$ and $g$ are continuous functions on $[a, b]$ and $g(x) >= 0, forall x in [a, b]$,
  then $exists c in (a, b)$ such that
  $
      integral_a^b f g = f(c) integral_a^b g.
  $
]

== Trapezoidal Rule for Integration

The trapezoidal rule approximates the area under a curve by dividing the interval $[a, b]$ into
$n$ subintervals and approximating the area under the curve on each subinterval with a trapezoid
instead of a rectangle (like in the Riemman sum).

If $f$ is twice differentiable on $[a, b]$, then the error $E$ in the trapezoidal rule with $n$
subintervals satisfies
$
    abs(E) <= (b - a)^3 / (12 n^2) dot max_(x in [a, b]) abs(f''(x)).
$

#example[
  Estimate the value of $integral_1^3 e^x / sqrt(x)$ using the trapezoidal rule. The height
  of each trapezoid is $0.25$.
]

Let $f(x) = e^x / sqrt(x)$. From $h = 0.25 = (3 - 1) / n => n = 8$. Thus, 8 trapezoids will
be needed to estimate the area under $f$.

#align(center)[
  #table(
    columns: 3,
    stroke: none,
    table.header[$i$][$x_i$][$f(x_i)$],
    [0], [1.00], [2.718281828],
    [1], [1.25], [3.121857647],
    [2], [1.50], [3.659283803],
    [3], [1.75], [4.350070736],
    [4], [2.00], [5.224851674],
    [5], [2.25], [6.325157229],
    [6], [2.50], [7.704885699],
    [7], [2.75], [9.452861944],
    [8], [3.00], [11.59639015]
  )
]

Therefore,
$
    integral_1^3 e^x / sqrt(x) &approx h/2 ( f(x_0) + 2 sum_(i=1)^7 f(x_i) + f(x_8))
      = 11.74407618.
$
To bound the error of the approximation, we need the higher order derivative
of $f$,
$
    f'''(x) = e^x (x^(-1/2) - 3/2 x^(-3/2) + 9/4 x^(-5/2) - 15/8 x^(-7/2))
$
Then
$
    x^3 - 1.5 x^2 + 2.25 x - 1.875 = 0      \
    (x^2 - 0.446 x + 1.78)(x - 1.054) = 0   \
    => x = 1.054
$
Therefore
$
    max_[1, 3] abs(f''(x)) = f''(1.054) = 2.02988825
$
Thus
$
    abs(E) <= 0.021144669
$

== Simpson's Rule

Let $f$ be a continuous function on $[a, b]$ and $n$ an even number. If $P = { x_0, x_1, ...,
x_n }$ is a regular partition of $[a, b]$, then
$
    integral_a^b f(x) d x approx (b - a) / (3n) (f(x_0) + 4f(x_1) + 2f(x_2) + ... + f(x_n)).
$

If $f$ is four times differentiable on $[a, b]$, then the error $E$ of Simpson's rule with $n$
subintervals satisfies
$
    abs(E) <= (b - a)^5 / (180 n^4) dot max_(x in [a, b]) abs(f^((4))(x)).
$

== Integration by Parts 

Let $f$ and $g$ be functions with their derivatives $f'$ and $g'$ integrable
on $[a, b]$, then
$
    integral_a^b f'(x) g(x) d x = f(x) g(x) Big(|)_a^b - integral_a^b f(x) g'(x) d x.
$

//TODO: #proof[]

== Integration by Substitution

If $f$ is continuous on $[a, b]$ and $phi$ is a function with a continuous derivative $phi'$
on $[alpha, beta]$ such that $phi([alpha, beta]) subset [a, b]$ with $phi(alpha) = a$ and
$phi(beta) = b$, then
$
    integral_a^b f(x) d x = integral_alpha^beta f(phi(t)) phi'(t) d t
$

//TODO: #proof[]

= The Logarithm

The function $ln: (0, +oo) -> RR$ by
$
    ln(x) = integral_1^x 1/t d t, quad forall x in (0, +oo).
$

#align(center)[
  #canvas({
    import draw: *

    set-style(stroke: 0.5pt)

    plot.plot(
      name: "plot",
      size: (4, 4), 
      x-tick-step: none,
      y-tick-step: none,
      axis-style: "school-book",
      {
        plot.add(domain: (0.2, 5), x => calc.ln(x))
        // plot.add(domain: (0.1, 12), x => 1/x)
      }
    )
  })
]

is called logarithm.

== Properties of the Logarithm

#proposition[
  $forall x in (1, +oo): ln(x) > 0$.
]

#proof[
  If $x > 1$ then $forall t in (1, x]: 1/t > 0$ Therefore,
  $
      ln(x) = integral_1^x 1/t d t > 0.
  $
]

#proposition[
  $forall x in (0, 1): ln(x) < 0$.
]

#proof[
  Let $x in (0, 1)$, then
  $
      ln(x) = integral_1^x 1/t d t = - integral_x^1 1/t d t
  $
  From $0 < x < 1 => 1/t > 0$ implies
  $
      integral_x^1 1/t d t > 0
  $
  Thus,
  $
      ln(x) = - integral_x^1 1/t d t < 0.
  $
]

#proposition[
  $
      integral 1/x d x = ln abs(x) + C.
  $
]

#proof[
  $
      d / (d x) ln abs(x) = d / (d x) integral_1^abs(x) 1/t d t
        = cases(
          d / (d x) integral_1^x    1/t d t = 1/x quad &x > 0,
          d / (d x) integral_1^(-x) 1/t d t = -1/x dot (-1) = 1/x quad &x < 0.
        )
  $
  Therefore
  $
      d / (d x) ln abs(x) = 1/x => integral 1/x d x = ln abs(x) + C.
  $
]

#proposition[
  $ln(1) = 0$.
]

#proposition[
  If $f(t) = 1/t$ and $a, b in RR$, then
  $
      integral_a^(a b) 1/t d t = integral_a^b 1/t d t.
  $
]<proposition_1>

#proof[
  Let $u = t / a$, then
  $
      d u = (d t) / a => d t = a d u.
  $
  Such that $t = a => u = 1$ and $t = a b => u = b$. Using integration by substitution
  $
      integral_a^(a b) 1/t d t = integral_a^b a/(a u) d u = integral_a^b 1/u d u
        = integral_a^b a/t (d t) / a = integral_a^b 1/t d t.
  $
]

#proposition[
  If $x_1, x_2 > 0$, then $ln(x_1 dot x_2) = ln(x_1) + ln(x_2)$.
]

#proof[
  By definition
  $
      ln(x_1 dot x_2) = integral_1^(x_1 dot x_2) 1/t d t = integral_1^x_1 1/t d t
        + integral_(x_1)^(x_1 dot x_2) 1/t d t.
  $
  From @proposition_1,
  $
      ln(x_1 dot x_2) = integral_1^x_1 1/t d t + integral_(x_1)^(x_1 dot x_2) 1/t d t
        = ln(x_1) + ln(x_2).
  $
]

#proposition[
  If $x > 0$, then $ln(1/x) = -ln(x)$.
]

#proof[
  Note that $x dot 1/x = 1$,
  $
      ln(x dot 1/x) = ln(1) = 0 quad "and" quad ln(x dot 1/x) = ln(x) + ln(1/x)
  $
  Thus,
  $
      ln(x) + ln(1/x) = 0 => ln(1/x) = -ln(x).
  $
]

#proposition[
  If $x_1, x_2 > 0$, then $ln(x_1 / x_2) = ln(x_1) - ln(x_2)$.
]

#proof[
  Note that $x_1 / x_2 = x_1 dot 1/x_2$. Therefore,
  $
      ln(x_1 / x_2) = ln(x_1) + ln(1/x_2) = ln(x_1) - ln(x_2).
  $
]

#proposition[
  If $x > 0$ and $r in RR$, then $ln(x^r) = r dot ln(x)$.
]

#proof[
  By definition,
  $
      ln(x^r) = integral_1^(x^r) 1/t d t.
  $
  Let $t = y^r => d t = r y^(r-1) d y$ such that $t = 1 => y = 1$ and $t = x^r => y = x$.
  Using integration by substitution,
  $
      ln(x^r) = integral_1^x (r y^(r-1)) / y^r d y = r dot integral_1^x 1/y d y
        = r dot integral_1^x 1/y d y.
  $
  Thus,
  $
      ln(x^r) = r dot ln(x).
  $
]

#proposition[
  The function $ln: (0, +oo) -> RR$ is injective.
]

#proof[
  Let $x_1, x_2 in (0, +oo)$ such that $ln(x_1) = ln(x_2)$ then,
  $
      integral_1^x_1 1/t d t = integral_1^x_2 1/t d t =>
      integral_1^x_1 1/t d t - integral_1^x_2 1/t d t = 0.
  $
  Suppose $x_1 < x_2$, then $forall t in [x_1, x_2]: 1/t > 0$. Using the FTC
  $
      integral_(x_1)^(x_2) 1/t d t > 0 =>
        (ln abs(x_2) + C) - (ln abs(x_1) + C) = ln(x_2) - ln(x_1) > 0
  $
  The result contradicts our hypotesis, so our assumption must be false. Similarly,
  $x_1 > x_2$ also contradicts our hypotesis. Therefore, $x_1 = x_2$.
]

#proposition[
  The function $ln: (0, +oo) -> RR$ is an increasing function.
]

#proof[
  From the definition,
  $
      ln(x) = integral_1^x 1/t d t, forall x > 0,
  $
  then
  $
      d / (d x) ln(x) = d / (d x) integral_1^x 1/t d t = 1/x > 0, forall x in (0, +oo).
  $
  Thus, the function $ln$ is an increasing function.
]

#proposition[
  The function $ln: (0, +oo) -> RR$ is concave downward.
]

#proof[
  Note that
  $
      ln''(x) = - 1/x^2 < 0, forall x in (0, +oo).
  $
  Thus, the function $ln$ is concave downward.
]

#proposition[
  The function $ln: (0, +oo) -> RR$ is surjective.
]

#proof[
  Let $y in RR$. Then,
  $
      y = ln(x) <=> x = e^y,
  $
  implies the existence of $x$ for any given $y$ such that $y = ln(x)$.
]

#proposition[
  The function $ln: (0, +oo) -> RR$ is bijective.
]

#proposition[
  Let $u$ be a differentiable function with $u(x) != 0$, then
  $
      integral frac(u'(x), u(x)) d x = ln abs(u(x)) + C.
  $
]

== Logarithmic derivation

#example[
  Determine $f'$ if
  $
      f(x) = frac((x + 2)(x^2 + 3), sqrt(x + 1)(x^3 + 3)) tan(x).
  $
  Take $abs(f(x))$ such that
  $
      abs(f(x)) = frac(abs(x + 2)abs(x^2 + 3), sqrt(x + 1)abs(x^3 + 3)) abs(tan(x)).
  $
  Evaluate $ln(abs(f(x)))$
  $
      ln abs(f(x)) = ln abs(x + 2) + ln abs(x^2 + 3) + ln abs(tan(x)) - ln sqrt(x + 1)
        - ln abs(x^3 + 3).
  $
  Now, derive both sides
  $
      (f'(x))/(f(x)) = 1/(x + 2) + (2x)/(x^2 + 3) + (sec^2(x))/tan(x) - 1/(2(x + 1))
        - (3x^2)/(x^3 + 3).
  $
  Therefore,
  $
      f'(x) = f(x)(1/(x + 2) + (2x)/(x^2 + 3) + (sec^2(x))/tan(x) - 1/(2(x + 1))
        - (3x^2)/(x^3 + 3)).
  $
]

= The Exponential

Note that the function $ln: (0, +oo) -> RR$ is bijective then $exists ln^*: RR -> (0, +oo)$
which is the function $exp: RR -> (0, +oo)$ defined by
$
    exp(x) = y <=> ln(y) = x, quad forall x in RR.
$

== Properties of the Exponential

#proposition[
  Let $x_1, x_2 in RR$. Then, $exp(x_1 + x_2) = exp(x_1) dot exp(x_2)$.
]

#proof[
  From $x_1, x_2 in RR => exists! y_1, y_2 in (0, +oo) slash x_1 = ln(y_1), x_2 = ln(y_2)$
  we get
  $
      exp(x_1) = y_1, quad exp(x_2) = y_2.
  $
  Moreover
  $
      x_1 + x_2 = ln(y_1) + ln(y_2) = ln(y_1 dot y_2).
  $
  Thus,
  $
      exp(x_1 + x_2) = y_1 dot y_2 = exp(x_1) dot exp(y_2).
  $
]

#proposition[
  Let $x_1, x_2 in RR$. Then,
  $
      exp(x_1 - x_2) = exp(x_1) / exp(x_2).
  $
]

#proof[
  From $x_1, x_2 in RR => exists! y_1, y_2 in (0, +oo) slash x_1 = ln(y_1), x_2 = ln(y_2)$
  we get
  $
      exp(x_1) = y_1, quad exp(x_2) = y_2.
  $
  Moreover
  $
      x_1 - x_2 = ln(y_1) - ln(y_2) = ln(y_1 / y_2).
  $
  Thus,
  $
      exp(x_1 - x_2) = y_1 / y_2 = exp(x_1) / exp(y_2).
  $
]

#proposition[
  If $r in RR$ then $exp(r dot x) = (exp(x))^r$.
]

#proof[
  Note that $x in RR => exists! y in (0, +oo) slash x = ln(y) => exp(x) = y$. Then
  $
      ln(y^r) = r dot ln(y) = r dot x => exp(r dot x) = y^r = (exp(x))^r.
  $
]

#proposition[
  $exp(ln(x)) = x, forall x in (0, +oo)$.
]

#proof[
  Let $x in (0, +oo)$ and $y = ln(x) => exp(y) = x$. Thus, $exp(ln(x)) = x$.
]

#proposition[
  $ln(exp(x)) = x, forall x in RR$.
]

#proof[
  Let $x in RR$ and $exp(x) = y => ln(y) = x$. Thus, $ln(exp(x)) = x$.
]

#remark(numbering: none)[
  Let $f: D_f -> RR$ a continuous and increasing function then $exists f^*: R_f -> D_f$.
  Furthermore, $f^*$ is a continuous and increasing function too.
]

#proposition[
  $exp: RR -> (0, +oo)$ is a continuous function. That is,
  $
      lim_(x -> x_0) exp(x) = exp(lim_(x -> x_0)) = exp(x_0), quad x_0 in RR.
  $
]

#proposition[
  $forall x in RR: exp(x) = e^x$.
]

#proof[
  $forall x in RR: x = ln(exp(x))$. Likewise,
  $
      ln(e^x) = x ln(e) = x => exp(x) = e^x.
  $
]

#proposition[
  $
      e = lim_(h -> 0) (1 + h)^(1/h).
  $
]

#proof[
  Let $f(x) = ln(x), forall x in (0, +oo)$ where
  $
      f'(x) = 1/x, quad forall x in (0, +oo).
  $
  Moreover,
  $
      f'(1) &= lim_(h -> 0) frac(f(1+ h) - f(1), h)     \
         1  &= lim_(h -> 0) frac(ln(1+ h) - ln(1), h)   \
            &= lim_(h -> 0) ln(1 + h)^(1/h)             \
            &= ln [lim_(h -> 0) (1 + h)^(1/h)]          \
       => e &= lim_(h -> 0) (1 + h)^(1/h).
  $
]

#proposition[
  $
      e = lim_(t -> +oo) (1 + 1/t)^(t).
  $
]

#example[
  Evaluate $
      alpha = lim_(x -> +oo) ((x + 1)/(x - 3))^x.
  $

  Indeed,
  $
      alpha = lim_(x -> +oo) (1 + 4/(x - 3))^x = lim_(x -> +oo) (1 + 1/((x - 3)/4))^x.
  $
  Let $t = (x - 3)/4$,
  $
      alpha = lim_(x -> +oo) (1 + 1/t)^(4t + 3) = [lim_(x -> +oo) (1 + 1/t)^t]^4
        [lim_(x -> +oo) (1 + 1/t)]^3 \
      => alpha = e^4 dot 1^3 = e^4.
  $
]

#remark(numbering: none)[
  Note that
  $
      d / (d x) e^x = e^x, forall x in RR.
  $
  Therefore,
  $
      integral e^x d x = e^x + C.
  $
]

#theorem[
  Let $f$ be a differentiable function. Then,
  - $
        d / (d x) e^f(x) = f'(x) e^f(x).
    $
  - $
        integral f'(x) e^f(x) = e^f(x) + C.
    $
    
]

== The Exponential on a Different Base

Let $a > 0$ with $a != 1$ and the function $f: RR -> RR$ defined by
$
    f(x) = a^x, forall x in RR.
$
$f$ is called the exponential function with base $a$ and is denoted by
$
    exp_a (x) := f(x) = a^x, forall x in RR.
$

#theorem[
  $a^x = e^(x ln(a)), forall x in RR.$
]

#proof[
  Let $x in RR$. Then
  $
      ln(a^x) = x ln(a) => exp(ln(a^x)) = exp(x ln(a))
  $
  Likewise
  $
      a^x = e^(x ln(a)), forall x in RR.
  $
]

#theorem[
  Let $f$ be a function defined by
  $
      f(x) = a^x = e^(x ln(a)), forall x in RR.
  $
  Satisfies the following
  - If $a in (0, 1)$ then the graph of $f$ is decreasing and is concave upward.
  - If $a > 1$ then the graph of $f$ is increasing and is concave downward.
]

#align(center)[
  #canvas({
    import draw: *

    set-style(stroke: 0.5pt)

    plot.plot(
      name: "plot",
      size: (3, 3),
      x-tick-step: none,
      y-tick-step: none,
      axis-style: "school-book",
      {
        plot.add(domain: (-2, 2), x => calc.pow(1.5, x))
      }
    )

    content(((0,-1), "-|", "plot.south"), $y = a^x, a > 1$)
    set-origin((5, 0))

    plot.plot(
      name: "plot",
      size: (3, 3),
      x-tick-step: none,
      y-tick-step: none,
      axis-style: "school-book",
      {
        plot.add(domain: (-2, 2), x => calc.pow(0.5, x))
      }
    )

    content(((0,-1), "-|", "plot.south"), $y = a^x, a in (0, 1)$)
  })
]

#theorem[
  - If $f(x) = a^x, forall x in RR$ then $f'(x) = ln(a) a^x, forall x in RR$.
  - $
        integral a^x d x = a^x/ln(a) + C.
    $
]

#proof[
  Note that
  $
      d / (d x) a^x = d / (d x) (e^(x ln(a))) = ln(a) e^(x ln(a)) = ln(a) a^x.
  $
  For the integral part,
  $
      d / (d x) (a^x/ln(a)) = a^x => integral d / (d x) (a^x/ln(a)) d x = integral a^x d x
  $
  Likewise
  $
      integral a^x d x = integral d / (d x) (a^x/ln(a)) d x = a^x/ln(a) + C.
  $
]

#theorem[
  - $
        d / (d x) a^f(x) = d / (d x) (e^(f(x) ln(a))) = f'(x) ln(a) a^f(x).
    $
  - $
        integral f'(x) a^f(x) d x = a^f(x)/ln(a) + C.
    $
]

== The Logarithm on a Different Base

Let $f: RR -> (0, +oo)$ defined as
$
    f(x) = a^x = e^(x ln(a)), quad forall x in RR, a > 0, a != 1.
$
The function $f$ is bijective, therefore $exists f^*: (0, +oo) -> RR$. Let $x in (0, +oo)$
then $exists! y in RR slash a^x = y <=> f^* (y) = x$. Moreover,
$
    x ln(a) = ln(y) => x = ln(y) / ln(a).
$
The function $f^*(y)$ is denoted as $log_a (y)$.

= Hyperbolic Functions

Let $sinh: RR -> RR$ and $cosh: RR -> RR$ be functions defined as
$
    sinh(x) = (e^x - e^(-x))/2, quad cosh(x) = (e^x + e^(-x))/2.
$

#align(center)[
  #canvas({
    import draw: *

    set-style(stroke: 0.5pt)

    plot.plot(
      name: "plot",
      size: (3, 3),
      x-tick-step: none,
      y-tick-step: none,
      axis-style: "school-book",
      {
        plot.add(domain: (-2, 2), x => calc.sinh(x))
      }
    )

    content(((0,-1), "-|", "plot.south"), $y = sinh(x)$)
    set-origin((5, 0))

    plot.plot(
      name: "plot",
      size: (3, 3),
      x-tick-step: none,
      y-tick-step: none,
      axis-style: "school-book",
      {
        plot.add(domain: (-2, 2), x => calc.cosh(x))
      }
    )

    content(((0,-1), "-|", "plot.south"), $y = cosh(x)$)
  })
]

#remark(numbering: none)[
  $sinh$ is an odd function and $cosh$ is an even function.
]

Likewise for $tanh(x)$ and $coth(x)$,
$
    tanh(x) = sinh(x) / cosh(x), quad coth(x) = cosh(x) / sinh(x).
$

#align(center)[
  #canvas({
    import draw: *

    set-style(stroke: 0.5pt)

    plot.plot(
      name: "plot",
      size: (3, 3),
      x-tick-step: none,
      y-tick-step: none,
      axis-style: "school-book",
      {
        plot.add(domain: (-2, 2), x => calc.tanh(x))
      }
    )

    content(((0,-1), "-|", "plot.south"), $y = tanh(x)$)
    set-origin((5, 0))

    plot.plot(
      name: "plot",
      size: (3, 3),
      x-tick-step: none,
      y-tick-step: none,
      axis-style: "school-book",
      {
        plot.add(domain: (-4, -0.1), x => 1 / calc.tanh(x))
        plot.add(domain: (0.1, 4), style: (stroke: (paint: blue)), x => 1 / calc.tanh(x))
      }
    )

    content(((0,-1), "-|", "plot.south"), $y = coth(x)$)
  })
]

And for $sech(x)$ and $csch(x)$,
$
    sech(x) = 1 / cosh(x), quad csch(x) = 1 / sinh(x).
$

#align(center)[
  #canvas({
    import draw: *

    set-style(stroke: 0.5pt)

    plot.plot(
      name: "plot",
      size: (3, 3),
      x-tick-step: none,
      y-tick-step: none,
      axis-style: "school-book",
      {
        plot.add(domain: (-4, 4), x => 1 / calc.cosh(x))
      }
    )

    content(((0,-1), "-|", "plot.south"), $y = sech(x)$)
    set-origin((5, 0))

    plot.plot(
      name: "plot",
      size: (3, 3),
      x-tick-step: none,
      y-tick-step: none,
      axis-style: "school-book",
      {
        plot.add(domain: (-4, -0.1), x => 1 / calc.sinh(x))
        plot.add(domain: (0.1, 4), style: (stroke: (paint: blue)), x => 1 / calc.sinh(x))
      }
    )

    content(((0,-1), "-|", "plot.south"), $y = csch(x)$)
  })
]

== Identities of Hyperbolic Functions

- $sinh(x + y) = sinh(x)cosh(y) + cosh(x)sinh(y)$.
- $cosh(x + y) = cosh(x)cosh(y) + sinh(x)sinh(y)$.
- $sinh(2x) = 2sinh(x)cosh(x)$.
- $cosh(2x) = cosh^2(x) + sinh^2(x)$.
- $cosh^2(x) - sinh^2(x) = 1$.
- $1 - tanh^2(x) = sech^2(x)$.
- $coth^2(x) - 1 = csch^2(x)$.
- $cosh(x) + sinh(x) = e^x$.
- $cosh(x) - sinh(x) = e^(-x)$.
- $cosh(2x) - 1 = 2 sinh^2(x)$.
- $cosh(2x) + 1 = 2 cosh^2(x)$.
- $
    cosh(x/2) = sqrt((cosh(x) + 1)/2), quad sinh(x/2) = plus.minus
      sqrt((cosh(x) - 1)/2).
  $
- $(cosh(x) + sinh(x))^n = cosh(n x) + sinh(n x), forall n in NN$.

== Derivatives of Hyperbolic Functions

- $sinh'(x) = cosh(x)$.
- $cosh'(x) = sinh(x)$.
- $tanh'(x) = sech^2(x)$.
- $coth'(x) = -csch^2(x)$.
- $sech'(x) = -sech(x)tanh(x)$.
- $csch'(x) = -csch(x)coth(x), quad x != 0$.

== Integrals of Hyperbolic Functions

- $
      integral sinh(f(x)) f'(x) d x = cosh(f(x)) + C.
  $
- $
      integral cosh(f(x)) f'(x) d x = sinh(f(x)) + C.
  $

== Inverse of Hyperbolic Functions

The function $y = sinh(x)$ is injective because $y' > 0$. Therefore, it admits an inverse function
defined as $y = sinh^(-1)(x), forall x in RR$.

#align(center)[
  #canvas({
    import draw: *

    set-style(stroke: 0.5pt)

    plot.plot(
      name: "plot",
      size: (3, 3),
      x-tick-step: none,
      y-tick-step: none,
      axis-style: "school-book",
      {
        plot.add(
          domain: (-2, 2),
          style: (stroke: (paint: red, dash: "dashed")),
          label: [$x$],
          x => x
        )
        plot.add(
          domain: (-2, 2),
          style: (stroke: (paint: blue, dash: "dashed")),
          label: [$sinh(x)$],
          x => calc.sinh(x)
        )
        plot.add(
          domain: (-2, 2),
          label: [$sinh^(-1)(x)$],
          x => calc.ln(x + calc.sqrt(x * x + 1))
        )
      }
    )
  })
]

For the function $y = cosh(x)$ to be injective, it is necessary to define it in an
interval such as $[0, +oo)$. Thus, the function $y$ admits an inverse function defined as
$y = cosh^(-1)(x), x >= 1$.

#align(center)[
  #canvas({
    import draw: *

    set-style(stroke: 0.5pt)

    plot.plot(
      name: "plot",
      size: (3, 3),
      x-tick-step: none,
      y-tick-step: none,
      axis-style: "school-book",
      {
        plot.add(
          domain: (-2, 2),
          style: (stroke: (paint: red, dash: "dashed")),
          label: [$x$],
          x => x
        )
        plot.add(
          domain: (-2, 2),
          style: (stroke: (paint: blue, dash: "dashed")),
          label: [$cosh(x)$],
          x => calc.cosh(x)
        )
        plot.add(
          domain: (1, 4),
          label: [$cosh^(-1)(x)$],
          x => calc.ln(x + calc.sqrt(x * x - 1))
        )
      }
    )
  })
]

Likewise for $y = sech(x), x >= 0$. The inverse function of $y$ is defined as $sech^(-1)(x),
forall x in (0, 1]$.

#align(center)[
  #canvas({
    import draw: *

    set-style(stroke: 0.5pt)

    plot.plot(
      name: "plot",
      size: (3, 3),
      x-tick-step: none,
      y-tick-step: none,
      axis-style: "school-book",
      {
        plot.add(
          domain: (-2, 2),
          style: (stroke: (dash: "dashed")),
          label: [$x$],
          x => x
        )

        plot.add(
          domain: (0.1, 1),
          label: [$sech^(-1)(x)$],
          x => calc.ln(1 + calc.sqrt(1 - x * x)) - calc.ln(x)
        )
      }
    )
  })
]

For $y = tanh(x)$, $y = coth(x)$ and $y = csch(x)$ it is not necessary to define the functions
in an integral as the functions are already injective in their domain.

#align(center)[
  #canvas({
    import draw: *

    set-style(stroke: 0.5pt)

    plot.plot(
      name: "plot",
      size: (3, 3),
      x-tick-step: none,
      y-tick-step: none,
      axis-style: "school-book",
      {
        plot.add(domain: (-0.9, 0.9), x => 1/2 * calc.ln((1 + x)/(1 - x)))
      }
    )

    content(((0,-1), "-|", "plot.south"), $y = tanh^(-1)(x), abs(x) < 1$)
    set-origin((4.5, 0))

    plot.plot(
      name: "plot",
      size: (3, 3),
      x-tick-step: none,
      y-tick-step: none,
      axis-style: "school-book",
      {
        plot.add(domain: (1.01, 4), x => 1/2 * calc.ln((x + 1)/(x - 1)))
        plot.add(domain: (-4, -1.01), style: (stroke: (paint: blue)), x => 1/2 * calc.ln((x + 1)/(x - 1)))
      }
    )

    content(((0,-1), "-|", "plot.south"), $y = coth^(-1)(x), abs(x) > 1$)
    set-origin((4.5, 0))

    plot.plot(
      name: "plot",
      size: (3, 3),
      x-tick-step: none,
      y-tick-step: none,
      axis-style: "school-book",
      {
        plot.add(domain: (-4, -0.1), x => calc.ln(1/x + calc.sqrt(1 + 1 / (x * x))))
        plot.add(domain: (0.1, 4), style: (stroke: (paint: blue)),  x => calc.ln(1/x + calc.sqrt(1 + 1 / (x * x))))
      }
    )

    content(((0,-1), "-|", "plot.south"), $y = csch^(-1)(x), x != 0$)
  })
]

== Identities of Inverse Hyperbolic Functions

- $sech^(-1)(x) = cosh^(-1)(x^(-1))$.
- $csch^(-1)(x) = sinh^(-1)(x^(-1))$.
- $coth^(-1)(x) = tanh^(-1)(x^(-1))$.
- $
      sinh^(-1)(x) = ln(x + sqrt(x^2 + 1)), x in RR.
  $
- $
      cosh^(-1)(x) = ln(x + sqrt(x^2 - 1)), x >= 1.
  $
- $ 
      tanh^(-1)(x) = 1/2 ln((1 + x)/(1 - x)), abs(x) < 1.
  $
- $ 
      coth^(-1)(x) = 1/2 ln((x - 1)/(x - 1)), abs(x) > 1.
  $
- $
      sech^(-1)(x) = ln((1 + sqrt(1 - x^2))/x), x in (0, 1].
  $
- $
      csch^(-1)(x) = ln(1/x + sqrt(1 + x^2)/abs(x)), x != 0.
  $

== Derivatives of Inverse Hyperbolic Functions

- $
      d / (d x) sinh^(-1)(x) = 1 / sqrt(x^2 + 1), quad x in RR.
  $

- $
      d / (d x) cosh^(-1)(x) = 1 / sqrt(x^2 - 1), quad x >= 1.
  $

- $
      d / (d x) tanh^(-1)(x) = 1 / (1 - x^2), quad abs(x) < 1.
  $

- $
      d / (d x) coth^(-1)(x) = 1 / (1 - x^2), quad abs(x) > 1.
  $

- $
      d / (d x) sech^(-1)(x) = - 1 / (x sqrt(1 - x^2)), quad x in (0, 1).
  $

- $
      d / (d x) sech^(-1)(x) = - 1 / (abs(x) sqrt(1 + x^2)), quad x != 0.
  $
