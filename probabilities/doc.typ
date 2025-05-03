#import "@preview/unequivocal-ams:0.1.2": ams-article
#import "@preview/great-theorems:0.1.2": *
#import "@preview/rich-counters:0.2.1": *

#show: ams-article.with(
  title: [Notas de Cálculo de Probabilidades],
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
    blocktitle: "Definición",
    counter: mathcounter_def
)

#let lemma = mathblock(
    blocktitle: "Lema",
    counter: mathcounter
)

#let theorem = mathblock(
    blocktitle: "Teorema",
    counter: mathcounter
)

#let proposition = mathblock(
    blocktitle: "Proposición",
    counter: mathcounter
)

#let corollary = mathblock(
    blocktitle: "Corolario",
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

#let proof = proofblock()

= Probabilidades

== Teorema de la Probabilidad Total

#theorem[
  Sea $A$ un evento, entonces se sabe que la intersección de $A$ y
  el evento universal $Omega$ es $A$. Se sabe además que $B$ y su
  complemento $B^c$ constituye una partición, Así
  $
      A = A inter Omega " y " B union B^c = Omega
  $
  Sustituyendo el segundo resultado en el primero en la ecuación
  anterior y aplicando la Ley de Morgan, tenemos
  $
      A = A inter (B union B^c) = (A inter B) union (A inter B^c).
  $
  Los eventos $(A inter B)$ y $(A inter B^c)$ son mutualmente
  exclusivos y por propiedad de la función de probabilidad, se tiene
  $
      PP(A) = PP(A inter B) + PP(A inter B^c).
  $
  En general, para $n$ eventos $B_i$, $i = 1, 2, ..., n$, una
  partición del espacio muestral $Omega$. Entonces para algún evento
  $A$, podemos escribir
  $
      PP(A) = sum _(i=1) ^n PP(A inter B_i), quad n >= 1.
  $
]

== El Teorema de Bayes

#lemma[
  Dados dos eventos $A$ y $B$ con probabilidades no nulas, se tiene
  que
  $
      PP(B | A) = (PP(B) PP(A | B)) / PP(A)
  $
]

#theorem[
  Sean $B_1, B_2, ..., B_k$ una partición del espacio muestral
  $Omega$, entonces para todo $A subset Omega$ con $PP(A) > 0$, se
  tiene
  $
    PP(B_j | A) = (PP(B_j) PP(A | B_j)) / PP(A) quad
    forall j = 1, ..., k,
  $
  con $P(A) = sum _(i=1) ^k PP(B_i) PP(A | B_i)$.
]

#remark[
  A las probabilidades $PP(B_j)$ se les llama probabilidades a priori
  y luego de conocer $PP(A)$, se obtiene las probabilidades
  condicionales $PP(B_j | A)$ que se les llama probabilidades a posteriori
  o actualizadas.
]

#pagebreak()

= Variables Aleatorias

#definition[
  Dado un experimento aleatorio $epsilon$ y asociado al mismo, un espacio de
  probabilidad $(Omega, cal(F), PP)$. Se define una variable aleatoria (v.a.),
  como una función real $X: Omega -> RR$ tal que
  $
      [X <= x] := { omega in Omega : X(omega) <= x } in cal(F) quad
      forall x in RR.
  $
]

#remark[
  Se puede definir a partir de una v.a. $X$ una función de probabilidad. Para
  lo cual se necesita:
  - Espacio muestral: $Omega_X = R_X$.
  - Espacio de eventos: $cal(G)$ generado por los intervalos $(-oo, x] thick
    forall x in RR$. (llamado $sigma$-álgebra de Borel)
  Luego, se define la función de probabilidad generada por $X$,
  $PP_X: cal(G) -> [0, 1]$ tal que
  $
      PP_X (A) := PP[X in A] quad forall A in cal(G).
  $
]

#definition[
  Se define la Función de Distribución (acumulada), denotada por $F_X$, de
  una v.a. $X$, como, $F_X: RR -> [0, +oo)$ tal que
  $
      F_X (x) := PP[X <= x] quad forall x in RR.
  $
]

#definition()[
  Se dice que $X$ es una variable aleatoria discreta si su rango, $R_X$, es
  finito o enumerable.
]

#definition[
  Se define la función de masa (cuantía o de frecuencia) respecto a una v.a.
  discreta $X$, como $p : R_X -> [0, 1]$ tal que
  $
      p(x) := PP[X = x] quad forall x in R_X.
  $
]

#remark[
  Se expresa la función de probabilidad generada por $X$, como
  $
      PP_X (A) = sum _(x in A) p(x) quad forall A in R_X.
  $
]

#remark[
  La función de masa generaliza la idea de probabilidad por frecuencia utilizada
  para variables aleatorias de rango finito.
]

#remark[
  De la definición de probabilidad, se deduce que
  $
      sum _(x in R_X) p(x) = 1.
  $
]

#proposition[
  Propiedades de $F_X$.
  + $0 <= F_X (x) <= 1$ para todo $x in RR$.
  + Se cumple que $lim_(x->-oo) F_X (x) = 0$ y $lim_(x->+oo) F_X (x) = 1$.
  + Si la v.a. $X$ tiene una imagen finita, entonces
    - $F_X (x) = 0$ para todo $x$ suficientemente pequeño.
    - $F_X (x) = 1$ para todo $x$ suficientemente grande.
  + $F_X$ es no decreciente:
    $
        F_X (x_2) <= F_X (x_1) " para " x_1 <= x_2.
    $
  + $F_X$ es continua por la derecha.
]

#definition[
  Se define la esperanza de una v.a. $X$, como el valor medio esperado (teórico):
  $
      mu = EE(X) := sum _(x in R_X) x p(x).
  $
]

#definition[
  La varianza de una v.a. $X$, se define como:
  $
      sigma^2 = op("Var")(X) := sum _(x in R_X) (x - mu)^2 p(x).
  $
]

#remark[
  La varianza representa la media de las desviaciones cuadráticas con respecto
  a la media esperada.
]

#proposition[
  Dado un espacio de probabilidad $(Omega, 2^Omega, PP)$ y $X$ una v.a. discreta.
  La esperanza de $X$ se puede hallar directamente sobre los puntos muestrales:
  $
      EE[X] = sum _(omega in Omega) X(omega) PP({omega}).
  $
]

#theorem[
  Sea $X$ una v.a. discreta con función de masa de probabilidad $p_X$ y
  $g: D_g subset RR -> RR$ tal que $R_X subset D_g$. La función de masa de
  probabilidad de la v.a. $Y = g compose X$ se obtiene como
  $
      p_Y(y) = sum _({x in R_X : g(x) = y}) p_X (x) quad forall y in R_Y.
  $
  Además, la esperanza de $Y$ se puede hallar como
  $
      EE(Y) = EE[g(X)] = sum _(x in R_X) g(x) p_X (x).
  $
]

#definition[
  *(Distribución de masa puntual $delta$.)* Se dice que una v.a. $X$ tiene
  distribución de masa puntual en $a$, $X tilde delta_a$, si es una variable
  aleatoria constante. Se tiene función de masa igual a
  $
      p_X (x) = cases(
        1 quad x = a,
        0 quad x != a.
      )
  $
  Y función de distribución
  $
      F_X (x) = cases(
        1 quad x >= a,
        0 quad x < a.
      )
  $
]

#definition[
  *(Distribución uniforme discreta.)* Una v.a. $X$ tiene distribución uniforme
  discreta, si dado $R_X := {x_1, ..., x_n}$, con $n in NN$. Su función de masa
  es de la forma:
  $
      p_X (x_i) = cases(
        1/n quad "para " i in {1, ..., n},
        0   quad "en otros casos."
      )
  $
]

#definition[
  Se dice que un experimento aleatorio es de Bernoulli si su espacio muestral
  es
  $
      Omega := {E, F}.
  $
  Es decir, solo hay dos casos posibles que denotaremos por:
  $
      E: "éxito" quad , quad F: "fracaso".
  $
]

#definition[
  *(Distribución de Bernoulli.)* Se dice que una v.a. $X$ tiene distribución de
  Bernoulli, $X tilde op("Be")(p)$, con probabilidad de éxito $p$. Si
  $
      X(E) = 1 quad , quad X(F) = 0.
  $
  Y
  $
      P(X = 1) = p quad , quad P(X = 0) = 1 - p,
  $
  para algún $p in (0, 1)$.
]

#remark[
  Para una v.a. con distribución de Bernoulli, se tiene

  - Función de masa:
  $
      p_X (x) = p^x (1 - p)^(1-x), quad x in {0, 1}.
  $
  - La esperanza:
  $
      mu = EE(X) = 0 times (1 - p) + 1 times p = p.
  $
  - La varianza:
  $
      sigma^2 &= op("Var")(X) = (0 - p)^2(1 - p) + (1 - p)^2 times p \
      &= p(1 - p)[p + 1 - p] = p(1 - p).
  $
]

#definition[
  *(Distribución binomial.)* Una v.a. $X$ tiene distribución binomial, $X tilde
  op("Bi")(n, p)$, si se verifica que
  + Consiste de $n$ experimentos de Bernoulli $epsilon_1, ..., epsilon_n$.
  + Los experimentos son independientes.
  + La probabilidad de éxito, $p$, es constante en cada ensayo.
  + Espacio muestral:
    $
        Omega = { w = (w_1, ..., w_n) : w_i = E or F }.
    $
  + Variable aleatoria:
    $
        X: Omega &-> RR \
           omega &-> X(omega) = "Número de éxitos".
    $
  + Dado $w in [X = x]$ cualesquiere
    $
        PP({w}) = product _(i=1) ^n PP({w_i}) = p^x (1 - p)^(n - x).
    $
  + El cardinal de $[X = x]$ se basa en dividir el conjunto de $n$ elementos:
    - $x$ repeticiones de $E$,
    - $n - x$ repeticiones de $F$,
    es decir $binom(n, x).$
  + Luego,
    $
        PP[X = x] &= sum _w PP({w}) \
        &= abs([X = x]) dot PP({w}) \
        &= binom(n, x) p^x (1 - p)^(n - x).
    $
  + La función de masa es
    $
        p_X (x) = cases(
          binom(n, x) p^x (1 - p)^(n - x) quad &"para" x in {0, ..., n},
          0 quad &"en otros casos".
        )
    $
]

#definition[
  *(Geométrica.)*
  + Experimento geométrico. \
    $epsilon:$ Repetir un experimento de Bernoulli hasta que ocurra un primer
    éxito.
  + Espacio muestral:
    $Omega = {E, italic("FE"), italic("FFE"), ...}$.
  + Variable aleatoria:
    $X$: Número de ensayos de Bernoulli hasta que resulte el primer éxito.
  + Rango: $R_X = {1, 2, ...}$ = $NN$.
  + $X tilde op("Ge")(p)$.
  + Función de masa, usando la independencia:
    $
        p_X (x) = (1 - p)^(x - 1)p quad forall x in R_X.
    $
  + Momentos:
    $
        EE(X) = 1 / p quad , quad op("Var")(X) = (1 - p) / p^2.
    $
]

#remark[
  Que el espacio muestral $Omega$ sea infinito indica que la probabilidad de éxito del
  evento se encuentra en el intervalo $(0, 1)$.
]

= Momentos

Para una v.a. $X$ (discreta o continua)

