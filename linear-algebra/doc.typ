#import "@preview/unequivocal-ams:0.1.2": ams-article
#import "@preview/great-theorems:0.1.2": *
#import "@preview/rich-counters:0.2.1": *
#import "@preview/fletcher:0.5.7" as fletcher: diagram, node, edge

#show: ams-article.with(
  title: [Linear Algebra],
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

#let v0 = $bold("0")$

#let vu = $bold("u")$
#let vv = $bold("v")$
#let vw = $bold("w")$
#let ve = $bold("e")$
#let vf = $bold("f")$

= Linear maps

#definition[
  Let $U$ and $V$ denote vector spaces over a field $FF$ and let $T: U -> V$.
  The function $T: U -> V$ is a linear map if
  - $forall vu, vv in V : T(vu + vv) = T(vu) + T(vv)$.
  - $forall lambda in FF, forall vu in V : T(lambda vu) = lambda T(vu)$.
]

#definition[
  Let $U$ and $V$ denote vector spaces over a field $FF$ and let $T: U -> V$
  a linear map, we define the sets $
      ker(T) &= { vu in U : T(vu) = v0 } subset.eq U \
      im(T)  &= { vv in V : vv = T(vu) " for some " vu in U } subset.eq V
  $
]

#proposition[
  The kernel of $T$ is a vector subspace of $U$.
]
#proof[
  Let $vu, vv in ker(T)$. Apply $T$ to the linear combination of $vu$ and
  $vv$,
  $
      T(alpha vu + beta vv) = alpha T(vu) + beta T(vv) = v0
      quad alpha, beta in FF
  $ Shows that $alpha vu + beta vv in ker(T)$. Thus, $ker(T)$ is a linear
  subspace of $U$.
]

#proposition[
  The image of $T$ is a vector subspace of $V$.
]
#proof[
  Let $vu', vv' in im(T)$. There exists $vu, vv in U$ such that $
      vu' = T(vu) " and " vv' = T(vv).
  $ We form the linear combination of $vu'$ and $vv'$, $
      alpha vu' + beta vv' = alpha T(vu) + beta T(vv)
      = T(alpha vu + beta vv) quad alpha, beta in FF
  $ Shows that $alpha vu' + beta vv' in V$ implies the existence
  of $alpha vu + beta vv in U$. Thus, $im(T)$ is a linear
  subspace of $V$.
]

#proposition[
  Let $U$ and $V$ denote vector spaces over a field $FF$ and let $T: U -> V$ be
  a linear map. $T$ is injective if and only if $ker(T) = { v0 }$.
]
#proof[
  We proceed by proving both directions of the equivalence. \
  $(arrow.r.double)$ Assume $T$ is injective. Let $vv in ker(T)$. $T(vv) = v0$
  implies $vv = v0.$ \
  $(arrow.l.double)$ Assume $ker(T) = { v0 }$. Let $vu, vv in U$ such that
  $T(vu) = T(vv).$ Then, $
      T(vu) - T(vv) = T(vu - vv) &= v0 => vu = vv.
  $
]

#pagebreak()

#remark[
  Let $U$ be a vector space, the set ${ vv_1, vv_2, ..., vv_n } subset U,
  n in NN$ is said to be linearly independent (l.i.) if $
      sum _(i=1)^n lambda_i vv_i = v0 => lambda_i = 0, quad lambda_i in FF.
  $
]

#proposition[
  Let $U$ and $V$ denote vector spaces over a field $FF$ and let $T: U -> V$ be
  a linear map. $T$ is injective is and only if $T$ maps a linearly independent
  set to a linearly independent set.
]<lemma_1>

#remark[
  A function $f$ is injective if $
      f(x_1) = f(x_2) => x_1 = x_2, quad x_1, x_2 in D(f).
  $
]

#proof(of: <lemma_1>)[
  We proceed by proving both directions of the equivalence. \
  $(arrow.r.double)$ Assume T is injective. Suppose the set ${ vu_1, vu_2 ...,
  vu_k } subset U$ is linearly independent and $t_i in FF$ satisfy $
    t_1 T(vu_1) + t_2 T(vu_2) + ... + t_k T(vu_k) = v0 \
    T(t_1 vu_1 + t_2 vu_2 + ... + t_k vu_k) = v0 =>
      t_1 vu_1 + t_2 vu_2 + ... + t_k vu_k = v0
  $ so $t_1 = ... = t_k = 0$. \
  $(arrow.l.double)$ Assume $T$ maps a linearly independent set to a linearly
  injective set. Suppose for contradiction that $T$ is not injective $=>$
  $ker(T) eq.not { v0 }$. So, there exists $vv eq.not v0$ such that
  $T(vv) = v0$. Consider the set ${ vv }$. Since $vv eq.not v0$, the set
  ${ vv }$ is l.i. But $
      T(vv) = v0 => { T(vv) } = { v0 }.
  $ Which is not l.i. Thus, $T$ must be injective.
]

#proposition[
  Let $T$ be a linear map. $T$ is surjective if and only if $T$ maps a spanning set
  to a spanning set.
]

#proposition[
  Let $T$ be a linear map. $T$ is bijective if and only if $T$ maps a basis to a
  basis.
]

#definition[
  Let $U$ and $V$ denote vector spaces over a field $FF$ and let $T: U -> V$
  a linear map. $T$ is said to be
  - a monomorphism if $T$ is injective.
  - an epimorphism if $T$ is surjective.
  - an isomorphism if $T$ is bijective.
]

#theorem[
  Let $V$ and $W$ denote vector spaces over a field $FF$ and let $B = { vv_1,
  vv_2, ..., vv_n }$ basis of $V$ and let ${ vw_1, vw_2, ..., vw_n } subset
  W$. There exists only one linear map $T$ such that $T(vv_i) = vw_i$, for all
  $i in I_n.$
]
#proof[
  Let $T$ from $V$ to $W$ be defined by $
      T: V -> W, quad vv mapsto sum _(i=1)^n alpha_i vw_i. $
  Let $vv in V$. Since $B$ is basis of $V$, we can represent $vv$ as the linear
  combination of the vectors in $B$, $
      vv = sum _(i=1)^n alpha_i vv_i, quad { alpha_i } _(i=1)^n subset KK.
  $ Our goal is to prove that $T$ is not only a linear map but is it also unique.
  Let us begin by showing that $T$ is a function.

  1. $T$ is well-defined. Let $vu, vv in V$ such that $vu = vv$. $B$ is basis of
    $V$, hence $
        vu = sum _(i=1)^n alpha_i vv_i " and "
        vv = sum _(i=1)^n beta _i vv_i, quad alpha_i, beta_i in FF. $
    $vu$ is equal to $vv$, we have $
        sum _(i=1)^n alpha_i vv_i = sum _(i=1)^n beta _i vv_i =>
        sum _(i=1)^n (alpha_i - beta _i) vv_i = v0 =>
        alpha_i = beta_i.
    $ Then, $
        T(vu) = T(sum _(i=1)^n alpha_i vv_i)
              = T(sum _(i=1)^n beta _i vv_i)
              = T(vv). $
  2. $T$ is a linear map. Let $vu$ and $vv$. $B$ is basis of $V$, hence $
        vu = sum _(i=1)^n alpha_i vv_i " and "
        vv = sum _(i=1)^n beta _i vv_i, quad alpha_i, beta_i in FF.
    $ Apply $T$ to the linear combination of $vu$ and $vv$,
    $
        T(delta vu + theta vv) &= T(
          delta sum _(i=1)^n alpha_i vv_i +
          theta sum _(i=1)^n beta _i vv_i)
        = T(sum _(i=1)^n (delta alpha_i + theta beta_i) vv_i) \
        &=  sum _(i=1)^n (delta alpha_i + theta beta_i) vw_i
        =  delta   sum _(i=1)^n alpha_i vw_i  + theta   sum _(i=1)^n beta_i vw_i \
        &= delta T(sum _(i=1)^n alpha_i vv_i) + theta T(sum _(i=1)^n beta_i vv_i)
        =  delta T(vu) + theta T(vv) quad delta, theta in FF. $
  3. $T$ is unique. Suppose $L: U -> V$ a linear map such that $L(vv_i) = vw_i$.
    Then, $
        L(vv) &= L(sum _(i=1)^n alpha_i vv_i) = sum _(i=1)^n alpha_i L(vv_i)
        = sum _(i=1)^n alpha_i vw_i = T(vv).
    $ 
]

#corollary[
  Let $T, L$ be linear maps. If both map to the same basis, then $T = L$.
]

// ---------------------------------------------------- //

#theorem()[
  Let $T: V -> W$ be any linear map and assume that $ker(T)$ and $im(T)$
  are both finite dimensional. Then $V$ is also finite dimensional and $
      dim V = dim(ker T) + dim(im T).
  $
]
#proof[
  Let ${ ve_1, ve_2, ..., ve_k }$ be any basis of $ker(T)$. From the Basis
  Extension Theorem, we know there exists $vf_1, vf_2, ..., vf_r in V$ such
  that ${ve_1, ..., ve_k, vf_1, ..., vf_r}$ is a basis of $V$. So, it suffices
  to show that $B = { T(vf_1), T(vf_2), ..., T(vf_r) }$ is a basis of $im(T)$.
  
  1. $B$ spans $im(T)$. If $vw$ lies in $im(T)$, then
    there exists $vv in V$ such that $vw = T(vv)$, so $
      vw &= T(vv) = T(s_1 ve_1 + ... + s_k ve_k + t_1 vf_1 + ... + t_r vf_r)
      quad s_i, t_j in FF \
      &= T(s_1 ve_1 + ... + s_k ve_k) + t_1 T(vf_1) + ... + t_r T(vf_r) \
      &= t_1 T(vf_1) + ... + t_r T(vf_r).
  $
  2. $B$ is linearly independent. Suppose that $t_i in FF$ satisfy $ 
      t_1 T(vf_1) + t_2 T(vf_2) + ... + t_r T(vf_r) = v0 \
      T(t_1 vf_1 + t_2 vf_2 + ... + t_r vf_r) = v0 \
  $ the linear combination $t_1 vf_1 + t_2 vf_2 + ... + t_r vf_r$ is in $ker(T)$.
    Thus, $
      t_1 vf_1 + t_2 vf_2 + ... + t_r vf_r = s_1 ve_1 + s_2 ve_2 + ... + s_k ve_k
      quad s_j in FF \
      t_1 vf_1 + ... + t_r vf_r + (-s_1) ve_1 + ... + (-s_k) ve_k = v0
  $ so $t_1 = ... = t_r = 0$.

  Note further that $k + r$ is the number of elements of the basis we defined
  for $V$, $dim V$.
]

== The First Isomorphism Theorem
#theorem[
  Let $T: V -> W$ be a linear map and let $pi: V -> V slash ker(T)$ be the
  canonical projection. There exists a linear map $overline(T): V slash
  ker(T) -> W$ defined by $
      overline(T)(vv + ker T) = T(vv),
  $ such that the diagram $
    #align(center)[
      #diagram(cell-size: 15mm,
        node((0, 0), $V$, name: <A>),
        node((1, 0), $W$, name: <B>),
        node((1, 1), $V slash ker(T)$, name: <C>),
        edge(<A>, <C>, "->", $pi$, label-side: right),
        edge(<A>, <B>, "->", $T$),
        edge(<C>, <B>, "->", $overline(T)$, label-side: right)
      )
    ]
  $ is commutative, in other words, $T = overline(T) compose pi$.
]

#remark[
  The map $pi: V -> V slash W$ is called the canonical projection from $V$
  onto the quotient space $V slash W$. It is a linear map whose kernel is
  exactly $W$, and it is surjective.
]

#proposition[
  The linear map $overline(T): V slash ker T -> im T$ is an isomorphism.
]
#proof[
  Our goal is to prove that $overline(T)$ is a bijective function. Let us
  begin by showing that $overline(T)$ is a function. Let $vu, vv in V$ such
  that $vu + ker T = vv + ker T$, then $vu - vv in ker T$, hence $T(vu - vv)
  = v0$ and therefore $T(vu) = T(vv)$. Thus, we have proved that $
      overline(T)(vu + ker T) = T(vu) = T(vv) = T(vv + ker T).
  $ Which proves that $overline(T)$ is well-defined.

  1. By definition, por every $vv in V$, $ 
        T(vv) = overline(T)(vv + ker T) = overline(T)(pi(vv)) = overline(T)
        compose pi
  $ thus, $T = overline(T) compose pi$.
  2. Since $im(overline(T)) = im(T)$, it suffices to show that $ker T = {
     overline(v0) }$. Let $overline(vu) in V slash ker(T)$. If $overline(T)
     (overline(vu)) = v0$, then $T(vu) = v0$. Therefore $vu in ker(T)$ and $
         overline(vu) = vu + ker T = ker T + ker T = v0 + ker T = overline(v0).
     $

  Thus, we have shown that $overline(T)$ is an isomorphism.
]

#remark[
  The existance of an isomorphism between $V$ and $W$ vector spaces is denoted
  by $V tilde.eq W$.
]
