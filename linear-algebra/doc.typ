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

== Space of Linear Maps

#definition[
  Let $V, W$ denote vector spaces over a field $FF$, the set $
      cal(L)(V, W) = { T: V -> W | T " is a linear map" }
  $ with the operations $
      (T + L)(vv) &= T(vv) + L(vv) quad vv in V \
      (lambda T)(vv) &= lambda T(vv) quad vv in V, lambda in FF \
  $ is a vector space.
]

#remark[
  If $W = FF$ we denote $cal(L)(V, FF)$ as $V^*$ and call it the dual
  space of $V$.
]

#pagebreak()

#proposition[
  Let $V$ be a vector space over a field $FF$. Then the vector space $cal(L)(
  FF, V)$ is isomorphic to $V$. That is, $
      cal(L)(FF, V) tilde.equiv V.
  $
]
#proof[
  We define a map $Phi: cal(L)(FF, V) -> V$ by $Phi(f) = f(1)$. We will show
  that this map is a vector space isomorphism.

  + $Phi$ is well-defined. For any $f in cal(L)(FF, V), f(1) in V$, so the
    map makes sense.
  + $Phi$ is linear. Let $f, g in cal(L)(FF, V)$, and $a, b in FF$
    $
        Phi(a f + b g) = (a f + b g)(1) = a f(1) + b f(1) =
        a Phi(f) + b Phi(g).
    $
  + $Phi$ is bijective.
    - Injective. If $Phi(f) = Phi(g)$, then $f(1) = g(1)$, so $
        f(lambda) = lambda f(1) = lambda g(1) = g(lambda),
      $ hence $f = g$.
    - Surjective. For any $vv in V$, define $f_vv : FF -> V$ by $f_vv
      (lambda) = lambda vv$. Then $f_vv in cal(L)(FF, V)$ and $Phi(f_vv) = f_vv (1)
      = vv$.
]

#proposition[
  Let $V$ be a finite-dimensional vector space over a field $FF$. Then $V$ is
  isomorphic to $V^*$. That is, $
      V tilde.equiv V^*
  $
]
#proof[
  Assume ${ vv_1, vv_2, ..., vv_n }$ basis of $V$. We define the linear map $
      f_j : V -> FF " by " f_j(vv_i) = cases(
        1 quad i = j,
        0 quad i != j
      )
  $ It suffices to show that the set $B = { f_1, f_2, ..., f_n }$ is a basis of
  $V^*$.

  + $B$ spans $im(T)$. Let $f in V^*$ and let $s_j = f(vv_j).$
    $
        f(vv) &= f(t_1 vv_1 + t_2 vv_2 + ... + t_n vv_n) quad t_i in FF \
        &= t_1 f(vv_1) + t_2 f(vv_2) +... + t_n f(vv_n) \
        &= t_1 s_1 + t_2 s_2 + ... + t_n s_n \
        &= s_1 f_1 (vv) + s_2 f_2 (vv) + ... + s_n f_n (vv)
    $
  + $B$ is linearly independent. Suppose that $r_i in FF$ satisfy $
        r_1 f_1 (vv) + r_2 f_2 (vv) + ... + r_n f_n (vv) = 0.
  $ Evaluate for $vv = vv_i$  $
        r_1 f_1 (vv) + r_2 f_2 (vv) + ... + r_n f_n (vv) =
        r_i = 0,
  $ so $r_1 = ... = r_n = 0$.
]

#remark[
  If $dim V = + infinity$, then $V tilde.equiv.not V^*$.
]

#proposition[
  Let $V, W$ be finite-dimensional vector spaces. Then, $
      dim cal(L)(V, W) = dim V dot dim W.
  $
]

#proposition[
  Let $U, V, W$ denote vector spaces over a field $FF$. From the sequence $
      U stretch(arrow, size: #2em)^T V stretch(arrow, size: #2em)^L W
  $ observe that if
  - $L compose T = id_U$. Then, $L$ is a left inverse of $T$.
  - $T compose L = id_V$. Then, $L$ is a right inverse of $T$.
  - $L compose T = id_U$ and $T compose L = id_V$. Then, $L$ is the inverse of $T$ and is
    denoted by $L = T^(-1)$. Thus, $T$ is invertible.
]

#proposition[
  Let $T$ be a linear map. Observe that if
  + $T$ admits an inverse, that inverse is uniquely determined.
  + $T$ is a monomorphism $<=>$ $T$ is left-invertible.
  + $T$ is an epimorphism $<=>$ $T$ is right-invertible.
  + $T$ is an isomorphism $<=>$ $T$ is invertible.
]

== Projections
#definition[
  Let $V$ be a vector space. Suppose that $V = U plus.circle S$ with $U < V$ and  $S < V$. We
  define the linear maps $P: V -> V$ and $Q: V -> V$ by $
      P(vu + vv) = vu, quad Q(vu + vv) = vv, quad vu in U, vv in S.
  $ Then $P$ is called the projection of $V$ onto $U$ and $Q$ is called the projection of $V$
  onto $S$.
]

#proposition[
  Let $P$ and $Q$ be projections on the vector space $V$. Then $P$ and $Q$ possess the following
  properties
  + $P^2 = P$ and $Q^2 = Q$.
  + $P compose Q = Q compose P = v0$.
  + $P + Q = id_V$.
]
#proof[
  Let $vu in U$ and $vv in S$.
  + $P^2(vu + vv) = P(P(vu + vv)) = P(vu) = vu = P(vu + vv)$.
  + $P compose Q (vu + vv) = P(vv) = v0$, and $Q compose P (vu + vv) = Q(vu) = v0$.
  + $(P + Q)(vu + vv) = P(vu + vv) + Q(vu + vv) = vu + vv$. Thus, $P + Q = id_V$.
]

#proposition[
  Let $P: V -> V$ be a linear map. Then $P$ is a projection if and only if $P$
  is idempotent, that is, $P^2 = P$.
]<idem>

#proof[
  + If $P$ is a projection, then $P^2 = P$.
  + Let $U = { vu in V : P(vu) = vu } < V$ and $S = ker(P) < V$. Then, $V = U plus.circle S$.
    - $U inter S = { v0 }$. Let $vu in U inter S$. Then, $P(vu) = vu = v0$.
    - $V = U plus S$. Let $vv in V$. Then, $vv = P(vv) + vv - P(vv)$.
]

#proposition[
  Let $P_1: V -> V$ and $P_2: V -> V$ be linear maps. Then $P_1 + P_2$ is a projection if and
  only if $P_1 compose P_2 = P_2 compose P_1 = v0$.
]

#proof[
  The proof is left to the reader.
]

#definition[
  Let $V$ be a vector space and $T: V -> V$ be a linear map. A subspace $W subset.eq V$ is
  called invariant under $T$ if $T(W) subset.eq W$.
]

#proposition[
  Let $V$ be a vector space. Suppose that $V = U plus.circle S$ with $U$ and $S$ subspaces of
  $V$. Let $P: V -> V$ be a projection over $U$ and let $T: V -> V$ be a linear map. Then, $U$
  is invariant under $T$ if and only if $P compose T = T compose P$.
]

#proof[
  The proof is left to the reader.
]

#proposition[
  Let $V$ be a vector space and let $T: V -> V$ be an involution, that is, $T^2 = id_V$. Then,
  there exists $P: V -> V$ a projection such that $T = 2P - id_V$.
]

#proof[
  Let $P: V -> V$ be defined by $P(vv) = 1/2 (T(vv) + id_V)$, $vv in V$. Then, $
      P^2(vv) &= P(P(vv)) = P(1/2 (T(vv) + id_V)) \
      &= 1/2 (T(1/2 (T(vv) + id_V)) + id_V) \
      &= 1/2 (1/2 T(T(vv) + id_V) + id_V) \
      &= 1/2 (1/2 (T(T(vv)) + T(id_V)) + id_V) \
      &= 1/2 (1/2 (T(vv) + T(vv)) + id_V) \
      &= 1/2 (T(vv) + id_V) = P(vv).
  $ Thus, from @idem, $P$ is a projection.
]

#pagebreak()

== Annhilator
#definition[
  Let $V$ be a vector space over a field $FF$, and $A subset.eq V$. The annhilator of $A$ in $V*$
  is the set $
      A^0 = { f in V* : f(vu) = 0 thick forall vu in A } subset.eq V.
  $
]

#proposition[
  Let $V$ be a vector space over $FF$ and $A subset.eq V$. Then,
  + $forall A subset.eq V, A^0 < V^* $.
  + $V^0 = { 0 }$.
  + ${ 0 }^0 = V^*$.
  + If $A without { 0 } != emptyset -> A^0 != V^0$.
  + If $A subset.eq B subset.eq V -> A^0 supset.eq B^0$.
]

#proof[
  The proof is left to the reader.
]

#proposition[
  Let $V$ be a finite-dimensional vector space over $FF$ and let $S$ be a subspace of $V$. Then
  + $V^* slash S^0 tilde.equiv S^*$.
  + $dim V = dim S + dim S^0$.
]

#proof[
  The proof is left to the reader.
]

#proposition[
  If the vector space $V$ is finitely generated and $S < V$. Then $S^(00) = S$.
]

#proof[
  The proof is left to the reader.
]

== Transpose of a Linear Map
#definition[
  Let $T: U -> V$ a linear map. The transpose of $T$ is defined as $T^T: V^* -> U^*$ by
  $T^T (f) = f compose T, forall f in V^*$ $
    #align(center)[
      #diagram(cell-size: 15mm,
        node((0, 0), $U$, name: <A>),
        node((1, 0), $V$, name: <B>),
        node((1, 1), $FF$, name: <C>),
        edge(<A>, <C>, "->", $f compose T$, label-side: right),
        edge(<A>, <B>, "->", $T$),
        edge(<B>, <C>, "->", $f$, label-side: left)
      )
    ]
  $
]

#proposition[
  Let $T: U -> V$ and $L: U -> V$ be a linear map. Then,
  + $forall alpha in FF, (alpha T)^T = alpha T^T$.
  + $(T + L)^T = T^T + L^T$.
  + $(L compose T)^T = T^T compose L^T$ for the sequence $U
      stretch(arrow, size: #2em)^T V
      stretch(arrow, size: #2em)^L W $.
  + If $T$ admits an inverse, then $(T^(-1))^T = (T^T)^(-1)$.
  + If $I: U -> U$ is the identity map in $U$, then $I^T: U^* -> U^*$ is the identity map in
    $U^*$.
]

#proof[
  The proof is left to the reader.
]

#proposition[
  Let $U$ and $V$ denote vector spaces and Let $T: U -> V$ be a linear map. Then,
  + $[T(vv)]^0 = ker T^T$.
  + $T^T (V^*) subset.eq [ker T]^0$.
  + If $U$ and $V$ are finitely generated, then $dim T(U) = dim T^T (V^*)$.
  + If $U$ and $V$ are finitely generated, then $[ker T]^0 = T^T (V^*)$.
]

#proof[
  The proof is left to the reader.
]
