#import "@preview/fletcher:0.5.1" as fletcher: diagram, node, edge
#import "@preview/cetz:0.2.2"
#import "@local/math-notes:0.1.0": *
#import "@preview/xarrow:0.3.1": xarrow

#show: math_notes.with(title: [ELLIPTIC CURVES \
  And MODULAR FORMS])

#let SL = math.op("SL")
#let PSL = math.op("PSL")

#let injlim = $limits(limits(lim)_(xarrow(#v(-50em), width: #1.8em)))$
#let projlim = $limits(limits(lim)_(xarrow(sym:arrow.l.long, #v(-50em), width: #1.8em)))$


#let cal(x) = math.class("unary", text(font: "Computer Modern Symbol", x))
#let racts = $arrow.ccw.half$

= Basic Concepts of Elliptic Curves <basic-concepts-of-elliptic-curves>
== Elliptic Curves <elliptic-curves>
An elliptic curve is a smooth, projective, algebraic curve of genus one with a distinguished point.

=== Long Weierstrass form <long-weierstrass-form>
Affine part $ y^2 + a_1 x y + a_3 y = x^3 + a_2 x^2 + a_4 x + a_6 $

#strong[Discriminant and $j$-invariant] \
Let
$
  b_2 & colon.eq a_1^2 + 4 a_2\
  b_4 & colon.eq a_1 a_3 + 2 a_4\
  b_6 & colon.eq a_3^2 + 4 a_6\
  b_8 & colon.eq a_1^2 a_6 - a_1 a_3 a_4 + a_2 a_3^2 + 4 a_2 a_6 - a_4^2\
  c_4 & colon.eq b_2^2 - 24 b_4\
  c_6 & colon.eq - b_2^3 + 36 b_2 b_4 - 216 b_6
$
Then the discriminant is defined as
$
  Delta = - b_2^2 b_8 - 8 b_4^3 - 27 b_6^2 + 9 b_2 b_4 b_6 = frac(c_4^3 - c_6^2, 1728)
$
And the $j$-invariant is defined as $ j = c_4^3 \/ Delta $ Invariant holomorphic differential form (Néron differential) $ omega = upright(d) p lr((z)) \/ p^prime lr((z)) = upright(d) z = frac(upright(d) x, 2 y + a_1 x + a_3) $

=== Short Weierstrass form <short-weierstrass-form>
Affine part $ y^2 = x^3 + a x + b $ with determinant $ Delta = - 16 lr((4 a^3 + 27 b^2)) eq.not 0 $ The $j$-invariant is defined as $ j = 1728 frac(4 a^3, 4 a^3 + 27 b^2) $

== Elliptic Integral <elliptic-integral>
=== Legendre form <legendre-form>
$
  y^2 = lr((1 - x^2)) lr((1 - k^2 x^2))
$
Complete elliptic integral of the first kind
$
  K(k)= integral_0^1 (upright(d) x) / sqrt((1-x^2)(1-k^2 x^2))
$

Let $omega = (upright(d) x) / y$, then
$
  integral_(C_1) omega = 4 K lr((k)) ,
$
where $C_1$ is a closed path around from $0$ to $1$ and back to $0$.

=== Carlson symmetric form <carlson-symmetric-form>
$
  y^2 = x lr((x + 1 - k^2)) lr((x + 1))
$ Complete elliptic integral of the first kind $ K(k)=R_F (0,1-k^2,1)=1/2 integral_0^infinity (upright(d) x)/sqrt(x(x+1-k^2)(x+1)) $ where $R_F$ is the Carlson symmetric form.

=== Carlson to Legendre <carlson-to-legendre>
Suppose $ E_1 : y^2 & = lr((1 - x^2)) lr((1 - k^2 x^2))\
E_2 : Y^2 & = X lr((X + 1 - k^2)) lr((X + 1)) $ There is a rational map $ phi.alt : E_1 & --> E_2\
lr((x , y))   & arrow.r.long.bar lr((1 / x^2 - 1 , y / x^3)) = lr((X , Y)) $ We can check it by substituting $X = 1 / x^2 - 1$ and $Y = y / x^3$ into $E_2$ $ y^2 / x^6 & = lr((1 / x^2 - 1)) lr((1 / x^2 - k^2)) 1 / x^2 $ Then we can use $phi.alt$ to pullback the integral on $E_2$ to $E_1$
$
  integral_0^infinity (upright(d) X) / sqrt(X(X+1-k^2)(X+1))=integral_0^infinity (upright(d) X) / Y =integral_1^0 (-2\/x^3) / (y\/x^3)upright(d) x=2integral_0^1 (upright(d) x) / y=2 integral_0^1 (upright(d) x) / sqrt((1-x^2)(1-k^2 x^2)).
$

// #pagebreak()


// = Elliptic Curves over $bb(CC)$
// ==

#pagebreak()

= Modular Forms

== Action of $SL_2(ZZ)$ <action-of-SL2>

=== Action of $SL_2(ZZ)$ on $HH$ <action-of-SL2-on-H>

The fundamental domain of the action of $SL_2(ZZ)$ on $HH$ is the set $F$ defined by

$
  F = {tau in HH mid(|) -1 / 2 <= op("Re")(tau) <= 1 / 2, med |tau| >= 1}
$

#{
  set align(center)
  v(1em)
  cetz.canvas(
    length: 1.2cm,
    {
      import cetz.draw: *
      scale(200%)
      set-style(stroke: (paint: luma(40%), thickness: 1pt))
      // Your drawing code goes here
      let rho_y = calc.sqrt(3) / 2
      let boundry_color_1 = teal.darken(10%)
      let boundry_color_2 = orange.lighten(10%).desaturate(15%)
      let boundry_point_color = red.darken(5%).desaturate(15%)

      let region_color = gradient.linear(aqua.desaturate(90%), aqua.desaturate(50%), angle: 90deg)

      let boundry_stroke_1 = (paint: boundry_color_1, thickness: 2pt)
      let boundry_stroke_2 = (paint: boundry_color_2, thickness: 2pt)


      rect((-0.5, 0), (0.5, 2.299), fill: region_color, stroke: none) // region


      line((0.5, 0), (0.5, rho_y))
      arc((1, 0), start: 0deg, delta: 180deg, fill: white)

      arc(
        (60deg, 1),
        start: 60deg,
        delta: 60deg,
        stroke: boundry_stroke_2,
        mark: (symbol: "straight", stroke: boundry_stroke_2, offset: 12%, scale: 0.7),
      ) // mark

      arc((60deg, 1), start: 60deg, delta: 60deg, stroke: boundry_stroke_2)

      line((-1.5, 0), (1.5, 0)) // x-axis


      line((0.5, 0), (0.5, rho_y))
      line((0.5, rho_y), (0.5, 2.3), stroke: boundry_stroke_1)
      mark((0.5, rho_y), (0.5, 1.8), symbol: "straight", stroke: boundry_stroke_1, scale: 0.7)


      line((-0.5, 0), (-0.5, 2.3))
      line((-0.5, rho_y), (-0.5, 2.3), stroke: boundry_stroke_1)
      mark((-0.5, rho_y), (-0.5, 1.8), symbol: "straight", stroke: boundry_stroke_1, scale: 0.7)

      circle((0, 1), radius: .04, fill: boundry_point_color, stroke: none)
      circle((60deg, 1), radius: .04, fill: rgb("#19bf13"), stroke: none)
      circle((120deg, 1), radius: .04, fill: rgb("#19bf13"), stroke: none)

      content((0.5, -0.15), $1 / 2$)
      content((-0.5, -0.15), $-1 / 2$)
      content((1, -0.15), $1$)
      content((-1, -0.15), $-1$)
      content((0, 0.85), $i$)
    },
  )
}

=== Action of $SL_2(ZZ)$ on $upright(bold(P))_RR^1=RR union.sq {oo}$ <action-of-SL2-on-H>

#proposition[Stabilizer of $oo$ in $SL_2(ZZ)$ and $PSL_2(ZZ)$][
  $SL_2(ZZ)$ and $PSL_2(ZZ)$ acts on $RR union.sq {oo}$ by Mobius transformations. The stabilizer of $oo$ is given by
  $
    op("Stab")_(SL_2(ZZ))(oo) = {
      plus.minus
      mat(1, n; 0, 1) mid(|) n in ZZ
    },quad
    op("Stab")_(PSL_2(ZZ))(oo) = {mat(1, n; 0, 1) mid(|) n in ZZ}.
  $
]
#proof[
  This follows from the fact that $op("Stab")_(PSL_2(RR))(oo)$ is consisting of upper triangular matrices.
]

#proposition[$SL_2(ZZ)$ Acts on $upright(bold(P))_QQ^1=QQ union.sq {oo}$ Transitively][
  The action of $SL_2(ZZ)$ on $QQ union.sq {oo}$ is transitive.
]<SL2-acts-on-H-transitively>
#proof[
  It is sufficient to show that for any $(a:c)in upright(bold(P))^1_QQ$, where $a$, $c$ are coprime integers, there exists $gamma in SL_2(ZZ)$ such $gamma oo = (a:c) $. Note that coprimeness guarantees that there exist $b,d in ZZ$ such that $a d - b c = 1$. So take $ gamma=mat(a,b;c,d)in SL_2(ZZ) $ and we have
  $
    gamma oo=mat(a,b;c,d) mat(1;..;0)=mat(a;..;c).
  $
]

== Modular Forms of Integral Weight <modular-forms-of-integral-weight>

=== Congruence Subgroup

#definition[Principal Congruence Subgroup of Level $N$][
  Let $N$ be a positive integer. The modulo $N$ reduction homomorphism $bb(Z) arrow.r bb(Z) \/ n bb(Z)$ induces group homomorphisms
  $
    pi_N : SL_2 (bb(Z)) --> SL_2 (bb(Z) \/ N bb(Z)).
  $
  The *principal congruence subgroup of
level $N$* in $ upright(S L)_2 (bb(Z))$ is the kernel of $pi_N$,
  and it is usually denoted by
  $
    Gamma (N) = ker pi_N = {
      mat( a, b; c, d) in upright(S L)_2 (bb(Z)) : mat(delim: "[", a, b; c, d) equiv mat( 1, ; , 1) med(mod med N)
    }.
  $
  where the matrix congruence is interpreted entrywise, i.e.
  $
    a &equiv d &equiv 1 med &(mod med N),\
    b &equiv c &equiv 0 med &(mod med N).
  $

]

#lemma[][
  $pi_N : SL_2 (bb(Z)) --> SL_2 (bb(Z) \/ N bb(Z))$ is surjective. And we have $|SL_2(ZZ): Gamma(N)|=|SL_2 (bb(Z) \/ N bb(Z))|<oo$.
]
#proof[
  For any matrix $B=mat(overline(a),overline(b);overline(c),overline(d)) in SL_2 (bb(Z) \/ N bb(Z))$, we need to find a matrix $A=mat(a',b';c',d') in SL_2 (bb(Z))$ such that $pi_N (A)=B$. That is, find integers $a',b',c',d' in ZZ$ such that $a' equiv a med (mod med N)$, $b' equiv b med (mod med N)$, $c' equiv c med (mod med N)$, $d' equiv d med (mod med N)$ and $a' d' - b' c' = 1$.
  - First we are to find $a',b' in ZZ$ such that $gcd(a',b')=1$ and $a' d - b' c equiv 1 med (mod med N)$. Suppose $a eq.not 0$. According to Chinese remainder theorem, there exists an integer $t$ such that
    $
      t equiv cases(
      1 quad & ( mod med p)\,  & quad forall"prime" p divides gcd (a , b) \
      0 quad & ( mod med p)\,  & quad forall"prime" p divides.not gcd (a , b) \, med p divides a )
    $
    Let $a'=a$, $b'=b+t N$. Then $a' d - b' c equiv 1 med (mod med N)$. Assume that $p$ is any prime factor of $a$.

    + If $p$ is also a prime factor of $b$, then #h(1fr)
      $
        b' equiv b+t N equiv N med (mod med p).
      $
      Note that
      $
        a d-b c equiv 1 med (mod med N)==>gcd(a,b,N)=1.
      $
      $p divides gcd(a,b)$ means $p$ is not a prime factor of $N$. So we have $p divides.not b'$.
    + If $p$ is not a prime factor of $b$, then #h(1fr)
      $
        b' equiv b+t N equiv b med (mod med p).
      $
      So again we have $p divides.not b'$.

    Thus we show that $gcd(a',b')=1$.

  - Then we construct $c'$ and $d'$. Suppose $a' d-b' c=1+k N$, where $k in ZZ$. It is sufficient to show that there exist $x,y in ZZ$ such that $c'=c+x N$, and $d'=d+y N$ and $a' d' - b' c' = 1$.
    Note that
    $
      a' d' - b' c' = 1 <==> a'(d+y N)-b'(c+x N)=a'd-b'c-k N <==>b'x-a'y=k.
    $
    Since $gcd(a',b')=1$ divides $k$, there exist integer solution $x^*,y^*$ such that $b'x^*-a'y^*=k$, which completes the proof.
]

#definition[Congruence Subgroup of $SL_2(ZZ)$][
  A subgroup $Gamma$ of $SL_2(ZZ)$ is called a *congruence subgroup* if it contains $Gamma(N)$ for some positive integer $N$.
]

#proposition[Properties of Congruence Subgroups][
  Let $Gamma$ be a congruence subgroup of $SL_2(ZZ)$.

  - $Gamma$ is a discrete subgroup of $SL_2(RR)$.

  - The index $|SL_2(ZZ):Gamma|$ is finite.
]
#proof[
  - It is clear that $upright(M)_2(ZZ)$ is a discrete subspace of $upright(M)_2(RR)$. Since any subspace of a discrete space is discrete, any concruence subgroup is discrete in $upright(M)_2(RR)$.
  - Suppose $Gamma$ has a subgroup $Gamma(N)$. Since $pi_N : SL_2 (bb(Z)) ->> SL_2 (bb(Z) \/ N bb(Z))$ is surjective, we have $|SL_2(ZZ):Gamma(N)|=|im pi_N|= |SL_2 (bb(Z) \/ N bb(Z))|<oo$. From
    $
      |SL_2(ZZ):Gamma|med |Gamma:Gamma(N)|=|SL_2(ZZ):Gamma(N)|
    $
    we see both $|SL_2(ZZ):Gamma|$ and $|Gamma:Gamma(N)|$ are finite.
]

#example[Congruence Subgroups $Gamma_1(N)$][
  Let $N$ be a positive integer. Define $P$ to be the subgroup of $SL_2(ZZ\/N ZZ)$ consisting of unipotent upper triangular matrices. For each $N$,
  $
    Gamma_1 (N) = pi_N^(-1)(P) = {
      mat( a, b; c, d) in upright(S L)_2 (bb(Z)) : mat(delim: "[", a, b; c, d) equiv mat( 1, *; , 1) med(mod med N)
    }
  $
  is a congruence subgroup of $SL_2(ZZ)$. We can check that
  $
    p_(12): Gamma_1 (N) &--> bb(Z)\/N bb(Z), \
    mat( a, b; c, d) &arrow.long.bar b med(mod med N).
  $
  is a surjective group homomorphism and we have the exact sequence
  $
    1 --> Gamma (N) --> Gamma_1 (N) -->^(p_12) bb(Z)\/N bb(Z) --> 1.
  $
  Therefore, $[Gamma_1 (N): Gamma (N)] = N$.
]
#proof[
  First we show that $p_(12)$ is a group homomorphism.
  $
    p_12 (
      mat( a_1, b_1; c_1, d_1) mat( a_2, b_2; c_2, d_2)
    ) = a_1 b_2 + b_1 d_2 med(mod med N) equiv b_1+ b_2 med(mod med N)
  $
  implies
  $
    p_12 (mat( a_1, b_1; c_1, d_1) mat( a_2, b_2; c_2, d_2)) = p_12 (mat( a_1, b_1; c_1, d_1)) +p_12 (
      mat( a_2, b_2; c_2, d_2)
    ).
  $
  Then we see $p_(12)$ is surjective because for any $b in bb(Z)\/N bb(Z)$, we can find $mat( 1, b; 0, 1) in Gamma_1 (N)$ such that
  $
    p_12 (mat( 1, b; , 1)) = b.
  $
  Finally we check the kernel of $p_(12)$ is
  $
    ker p_(12) = {mat( a, b; c, d) in Gamma_1 (N) : b equiv 0 med(mod med N)} = Gamma (N).
  $
]


#example[Hecke Congruence Subgroups $Gamma_0(N)$][
  Let $N$ be a positive integer. Define $SL_2^◹(ZZ\/N ZZ)$ to be the subgroup of $SL_2(ZZ\/N ZZ)$ consisting of upper triangular matrices. The *Hecke congruence subgroup of level $N$* is defined as
  $
    Gamma_0 (N) = pi_N^(-1)(SL_2^◹(ZZ\/N ZZ)) = {
      mat( a, b; c, d) in upright(S L)_2 (bb(Z)) : mat(delim: "[", a, b; c, d) equiv mat( *, *; , *) med(mod med N)
    }.
  $
]

#proposition[][
  + $
      Gamma (N) subset.eq Gamma_1 (N) subset.eq Gamma_0 (N) subset.eq upright(S L)_2 (bb(Z)).
    $

  + If $N | M$, then $Gamma (M) subset.eq Gamma (N)$.
]

#definition[Cusp of a Congruence Subgroup][
  Let $Gamma$ be a congruence subgroup of $SL_2(ZZ)$. Then $Gamma$ acts on $QQ union {oo}$ through Mobius transformations. A *cusp* of $Gamma$ is a $Gamma$-orbit in $upright(bold(P))^1_QQ=QQ union.sq {oo}$.
]

#proposition[Congruence Subgroups have Finite Number of Cusps][
  Let $Gamma$ be a congruence subgroup of $SL_2(ZZ)$. Then $Gamma$ has a finite number of cusps
  $
    lr(|Gamma\\ upright(bold(P))^1_QQ|) <= lr(|SL_2(ZZ):Gamma|).
  $
  $SL_2(ZZ)$ only has one cusp.
]
#proof[
  @SL2-acts-on-H-transitively shows that $SL_2(ZZ)$ only has one cusp.
  Now consider a general congruence subgroup $Gamma$. Suppose under the left action of $Gamma$, $SL_2(ZZ)$ has coset decomposition
  $
    SL_2(ZZ)= union.sq.big_(i=1)^n Gamma g_i,
  $
  where $n=lr(|SL_2(ZZ):Gamma|)$. Then
  $
    upright(bold(P))^1_QQ = SL_2(ZZ)oo=union.big_(i=1)^n Gamma g_i oo
  $
  and we see the number of cusps of $Gamma$ is not greater than $n$.

]



#definition[Factor of Automorphy][
  For any $gamma = mat( a, b; c, d) in upright("GL")_2 (bb(C))$, the *factor of automorphy* of $gamma$ is defined as
  $
    j(gamma, tau) = c tau + d, quad tau in bb(H).
  $
]

#lemma[Properties of Factor of Automorphy][
  - For any $gamma_1,gamma_2 in upright("GL")_2 (bb(R))^+$, we have
  $
    j(gamma_1 gamma_2, tau) = j(gamma_1, gamma_2 tau) j(gamma_2, tau), quad tau in bb(H).
  $
  - For any $gamma = mat(cos theta,- sin theta; sin theta,cos theta)  in op("SO")_2 (bb(R))$, we have
  $
    j(gamma, i) = e^(i theta)=cos theta + i sin theta.
  $
]<properties-of-factor-of-automorphy>
#proof[
  Note that for any $gamma = mat( a, b; c, d) in upright("GL")_2 (bb(R))^+$, we have

  $
    gamma mat( tau; 1) =mat( a, b; c, d) mat( tau; 1)= mat(a tau + b; c tau + d) = j(gamma, tau) mat(gamma tau; 1).
  $
  On the one hand, we have
  $
    gamma_1 gamma_2 mat( tau; 1) = j(gamma_1 gamma_2, tau) mat(gamma_1 gamma_2 tau; 1) ,
  $
  and on the other hand, we have
  $
    gamma_1 gamma_2 mat( tau; 1) = gamma_1 j(gamma_2, tau) mat(gamma_2 tau; 1) =
    j(gamma_2, tau) gamma_1 mat(gamma_2 tau; 1) = j(gamma_2, tau) j(gamma_1, gamma_2 tau) mat(gamma_1 gamma_2 tau; 1).
  $
  That completes the proof of the first property. The second property is a direct computation.
]

#definition[Weight-$k$ Operator][
  For any integer $k in ZZ$, and $gamma in op("GL")_2(RR)^+$, the *weight-$k$ operator* is defined as
  $
    [gamma]_k : op("Hom")_(sans("Set")) (HH, CC) & --> op("Hom")_(sans("Set")) (HH, CC)\
    f & arrow.bar.long f[gamma]_k
  $
  where
  $
    (f[gamma]_k)(tau) = (det gamma)^(k / 2) j (gamma , tau)^(- k) f (gamma tau) = (det gamma)^(k / 2) (
      c tau + d
    )^(-k) f(gamma tau).
  $
  Specially, for $gamma in upright(S L)_2 (bb(Z))$,
  $
    (f[gamma]_k)(tau) = j (gamma , tau)^(- k) f (gamma tau) = (c tau + d)^(-k) f(gamma tau).
  $
]

#proposition[][
  $op("GL")_2(RR)^+$ acts on $op("Hom")_(sans("Set")) (HH, CC)$ on the right by
  $
    op("Hom")_(sans("Set")) (HH, CC) times op("GL")_2(RR)^+ & --> op("Hom")_(sans("Set")) (HH, CC)\
    (f, gamma) & arrow.bar.long f[gamma]_k
  $
]
#proof[
  For any $f in op("Hom")_(sans("Set")) (HH, CC)$ and $gamma_1, gamma_2 in op("GL")_2(RR)^+$, by @properties-of-factor-of-automorphy we have
  $
    (f[gamma_1 gamma_2]_k)(tau)& = (det gamma_1 gamma_2)^(k / 2) j(gamma_1 gamma_2, tau)^(-k) f(gamma_1 gamma_2 tau)\
    & = (det gamma_1 gamma_2)^(k / 2) j(gamma_1 ,gamma_2 tau)^(-k) j(gamma_2 , tau)^(-k) f(gamma_1 gamma_2 tau)\
    & = (det gamma_2)^(k / 2) j(gamma_2,tau)^(-k)(
      (det gamma_1)^(k / 2) j(gamma_1, gamma_2 tau)^(-k)f(gamma_1 gamma_2 tau)
    )\
    & = (det gamma_2)^(k / 2) j(gamma_2,tau)^(-k)(f[gamma_1]_k)(gamma_2 tau)\
    &= ((f[gamma_1]_k)[gamma_2]_k)(tau).
  $
]

For $N in ZZ_(>=1)$, we have a surjective holomorphic complex Lie group homomorphism
$
  q_N: bb(C) &--> bb(C)^* = {z in CC mid(|) z eq.not 0}\
  tau &arrow.bar.long e^((2 pi i tau) / N).
$
The kernel of $q_N$ is the subgroup of $H$ given by
$
  ker q_N = {tau in bb(H) mid(|) e^((2 pi i tau) / N ) = 1} = N bb(Z).
$
By restricting $q_N$ to the upper half plane $bb(H)$, we get a surjective holomorphic semigroup homomorphism
$
  q_N: bb(H) &--> bb(D)^*={z in CC mid(|) 0<|z|<1}\
  tau & arrow.bar.long e^((2 pi i tau) / N ).
$
And we have
$
  q_N(tau_1) = q_N(tau_2) <==> tau_1 equiv tau_2 med(mod med N) <==> tau_1 - tau_2 in N bb(Z).
$
$q_N$ has the following universal property: for any holomorphic function $f: bb(H) --> bb(C)$ such that $f(tau + N) = f(tau)$, there exists a unique holomorphic function $tilde(f): bb(D)^* --> bb(C)$ such that $f = tilde(f) circle.tiny q_N$.
#commutative_diagram($
  HH edge("d", "->>", q_N) edge(->, f) &CC\
  DD^* edge("ru", "-->", tilde(f), #right)
$)

This motivates the following definition.
#definition[$q$-expansion of $N ZZ$-periodic Function][
  Let $N in ZZ_(>=1)$ and $f: bb(H) --> bb(C)$ be a holomorphic function such that $f(tau + N) = f(tau)$. Suppose $f = tilde(f) circle.tiny q_N$ and $tilde(f)$ has Laurent expansion $tilde(f)(q)=limits(sum)_(n in ZZ)  a_n q^n$. Then $f$ can be written as
  $
    f(tau) = sum_(n in ZZ) a_n q_N^n (tau) = sum_(n in ZZ) a_n e^((2 pi i n tau) / N),
  $
  which calls the *$q$-expansion* of $f$. Write $tau = x + i y$ and fix some $y>0$. Then $f$ as a function of $x$ is a periodic function with period $N$ and
  $
    f(x+i y) = sum_(n in ZZ) a_n e^((-2 pi n y) / N) e^((2 pi i n x) / N)
  $
  is the Fourier series of the function $x |-> f(x + i y)$.
]

Since $q_N (x + i y) -> 0$ as $y -> oo$ uniformly with respect to $x$, it is sensible to transfer the behavior of $f$ at infinity to the behavior of $q$-expansion of $f$ at $q = 0$.

#definition[Meromorphicity of $N ZZ$-periodic Holomorphic Function at $oo$][
  Suppose $f: bb(H) -> bb(C)$ is a $N ZZ$-periodic holomorphic function with $q$-expansion
  $
    tilde(f)(q) = sum_(n in ZZ) a_n q^n_N.
  $
  Then we say

  - $f$ is *meromorphic at $oo$* if there exist only finitely many $n < 0$ such that $a_n eq.not 0$.

  - $f$ is *holomorphic at $oo$* if $a_n = 0$ for all $n < 0$.

  - $f$ *vanishes at $oo$* if $a_n = 0$ for all $n <= 0$.
]
If $f$ is $f: bb(H) --> bb(C)$ is a $N ZZ$-periodic holomorphic function, then for any $d in ZZ_(>=1)$, $f$ is also a $d N ZZ$-periodic holomorphic function and we have $q_N=q_(d N)^d$
. The $q$-expansion of $f$ with respect to $q_(d N) $ is given by
$
  f(
    q
  ) = sum_(n in ZZ) a_n q^n_(N)= sum_(n in ZZ) a_n e^((2 pi i n tau) / (N))= sum_(n in ZZ) a_n q^(d n)_(d N) = sum_(n in ZZ) a_n e^((2 pi i d n tau) / (d N)).
$

#lemma[$f: bb(H) -> bb(C)$ is Fixed by ${[gamma]_k mid(|)gamma in Gamma}$ Implies $f[alpha]_k$ is $N ZZ$-periodic][
  Suppose $Gamma$ is a congruence subgroup of level $N$ and $f: bb(H) -> bb(C)$ is a function. Consider the right action $op("Hom")_(sans("Set")) (HH, CC) racts op("GL")_2(RR)^+$ given by weight-$k$ operator $f dot gamma = f[gamma]_k$. If $Gamma subset.eq op("Stab")_(op("GL")_2(RR)^+)(f)$, then for any $alpha in SL_2(ZZ)$,
  $
    mat(1,N;,1) in op("Stab")_(op("GL")_2(RR)^+)(f[alpha]_k),
  $
  or equivalently,
  $
    (f[alpha]_k) (tau+N)=(f[alpha]_k) (tau).
  $
]<f-is-fixed-by-gamma-implies-f-alpha-is-N-periodic>
#proof[
  Note that $Gamma(N)triangle.small.l SL_2(ZZ)$. For any $alpha in SL_2(ZZ)$, we have
  $
    alpha mat(1,N;,1) alpha^(-1)in alpha Gamma(N) alpha^(-1)=Gamma(N)subset.eq Gamma subset.eq op("Stab")_(op("GL")_2(
      RR
    )^+)(f),
  $
  which implies
  $
    mat(1,N;,1) in alpha^(-1) op("Stab")_(op("GL")_2(RR)^+)(f) alpha=op("Stab")_(op("GL")_2(RR)^+)(f[alpha]_k).
  $
]
#definition[Meromorphicity at Cusps][
  Let $Gamma$ be a congruence subgroup of level $N$ and $f: bb(H) -> bb(C)$ be a holomorphic function. Consider the right action $op("Hom")_(sans("Set")) (HH, CC) racts op("GL")_2(RR)^+$ given by weight-$k$ operator $f dot gamma = f[gamma]_k$. Suppose $Gamma subset.eq op("Stab")_(op("GL")_2(RR)^+)(f)$ and $x=alpha oo$ for some $alpha in SL_2(ZZ)$.
  Then we say

  - $f$ is *meromorphic at $Gamma x in Gamma\\ upright(bold(P))^1_QQ $* if $f[alpha]_k$ is meromorphic at $oo$.

  - $f$ is *holomorphic at $Gamma x in Gamma\\ upright(bold(P))^1_QQ $* if $f[alpha]_k$ is holomorphic at $oo$.

  - $f$ *vanishes at $Gamma x in Gamma\\ upright(bold(P))^1_QQ $* if $f[alpha]_k$ vanishes at $oo$.

]

#remark[
  We should check meromorphicity at a cusp is a well-defined property. First, we show that the meromorphicity of $f$ at $x in upright(bold(P))^1_QQ$ is well-defined. That is, if there exist $alpha,beta in op("SL")_2(ZZ)$ such that $alpha oo = beta oo$, then the meromorphicity of $f[alpha]_k$ and $f[beta]_k$ at $oo$ are equivalent. Consider $eta :=alpha^(-1)
beta in op("Stab")_(op("SL")_2(ZZ))(oo)$. Then $eta$ can be written as $ eta = plus.minus mat(1, m; , 1) $ for some $m in ZZ$ and we have
  $
    f[beta]_k (tau) = f[alpha eta]_k (tau)= (plus.minus 1)^(-k) f[alpha]_k (tau +m) .
  $
  From @f-is-fixed-by-gamma-implies-f-alpha-is-N-periodic, we know both $f[alpha]_k$ and $f[beta]_k$ are $N ZZ$-periodic and have $q$-expansions
  $
    f[alpha]_k (tau) = sum_(n in ZZ) a_n e^((2 pi i n tau) / N),quad f[beta]_k (
      tau
    ) = sum_(n in ZZ) b_n e^((2 pi i n tau) / N).
  $
  Since
  $
    f[beta]_k (tau) = sum_(n in ZZ) b_n e^((2 pi i n tau) / N)= (plus.minus 1)^(-k) f[alpha]_k (tau +m) =(
      plus.minus 1
    )^(-k)sum_(n in ZZ) a_n e^((2 pi i n (
      tau
      +m
    )) / N),
  $
  we get $b_n = (plus.minus 1)^(-k) a_n e^((2 pi i n m) / N)$ for all $n in ZZ$. Therefore, $f[alpha]_k$ is meromorphic at $oo$ if and only if $f[beta]_k$ is meromorphic at $oo$.

  Second, we need to show that for any $gamma in Gamma$, the meromorphicity of $f$ at $x$ and $gamma x$ are equivalent. It is sufficient to show that for any $gamma in Gamma$, the meromorphicity of $f[alpha]_k$ and $f[gamma alpha]_k$ at $oo$ are equivalent. This follows from the fact that
  $
    f[gamma alpha]_k = f[gamma]_k [alpha]_k = f[alpha]_k.
  $
]

#definition[Modular Form of Weight $k$ and Level $Gamma$][
  A *modular form of weight $k$ and level $Gamma$* is a holomorphic function $f: bb(H) -> bb(C)$ such that

  + #emph[Automorphy condition]: For any $gamma in Gamma$, $f$ is fixed by the action of $[gamma]_k$ , i.e. #h(1fr)
    $
      f[gamma]_k (tau) = (c tau + d)^(-k) f(gamma tau) = f(tau), quad forall tau in bb(H)
    $
    or equivalently
    $
      f(gamma tau)=(c tau + d)^k f(tau), quad forall tau in bb(H).
    $

  + #emph[Growth condition]: $f$ is holomorphic at all cusps. That is, for any cusp $Gamma x in Gamma\\ upright(bold(P))^1_QQ$, there exists $alpha in op("SL")_2(ZZ)$ such $x = alpha oo$ and $f[alpha]_k $ is holomorphic at $oo$.

  All modular forms of weight $k$ and level $Gamma$
  form a $CC$-vector space, denoted by $M_k (Gamma)$. If $f$ is a modular form of level $Gamma(N)$, then $f$ is called a *modular form of level $N$*.
]

#definition[Cuspidal Form][
  A modular form $f$ of weight $k$ and level $Gamma$ is called a *cuspidal form* if $f$ vanishes at all cusps. The space of cuspidal forms of weight $k$ and level $Gamma$ is denoted by $S_k (Gamma)$.
]

#proposition[Graded $CC$-algebra $M(Gamma)$][
  Define
  $
    M(Gamma) := plus.big_(k in ZZ) M_k (Gamma).
  $
  as the direct sum of $CC$-vector spaces. Then $M(Gamma)$ is a graded $CC$-algebra where the multiplication is given by the multiplication of modular forms.
  $
    S(Gamma) := plus.big_(k in ZZ) S_k (Gamma)
  $
  is a graded ideal of $M(Gamma)$.
]
#proof[
  For any $f in M_k (Gamma)$, $g in M_l (Gamma)$, and $gamma in Gamma$, we have
  $
    (f g) [gamma]_(k+l) = f[gamma]_k g[gamma]_l = f g.
  $

  Given any $alpha oo in upright(bold(P))^1_QQ$, since both $f[alpha]_k$ and $g[alpha]_l$ are holomorphic at $oo$, we see $(f g)[alpha]_(k+l)=f[alpha]_k g[alpha]_l$ is also holomorphic at $oo$. Thus we show that $f g in M_(k+l) (Gamma).$

  To show that $S(Gamma)$ is a graded ideal of $M(Gamma)$, it is sufficient to show that $S(Gamma)$ is the ideal generated by $S_k (Gamma)$ for all $k in ZZ$. This follows from the fact that
  for any $f in S_k (Gamma)$ and $g in M_l (Gamma)$, we have $f g in S_(k+l) (Gamma)$.

]

#definition[Meromorphic Modular Form][
  A *meromorphic modular form* of weight $k$ and level $Gamma$ is a meromorphic function $f: bb(H) -> bb(C)$ such that

  + For any $gamma in Gamma$, $f$ is fixed by the action of $[gamma]_k$ , i.e. #h(1fr)

    $
      f(gamma tau)=(c tau + d)^k f(tau), quad forall tau in bb(H).
    $

  + $f$ is meromorphic at all cusps.

]

#definition[Modular Function][
  Meromorphic modular forms of weight $0$ are called *modular functions*. Equivalently, a modular function of level $Gamma$ is a meromorphic function $f: Gamma\\ bb(H) -> bb(C)$ which is also meromorphic at all cusps.
]


#pagebreak()

= Number Theory <number-theory>

== $p$-adic Numbers


#definition[$p$-adic Integer][
  Let $p$ be a prime number. The $p$-adic integer topological ring is defined as
  $
    ZZ_p = projlim_n ZZ \/ p^n ZZ.
  $
  The universal property of $ZZ_p$ is given by the following commutative diagram

  #commutative_diagram($
    &&&&&G edge("d", "-->") edge("ddr", "->")\
    &&&&&ZZ_p edge("d", pi_m, "->") edge("dr", "->") edge("dll", "->") edge("dllll", "->") edge("dlllll", "->") \
    ZZ\/p ZZ edge("<-")
    & ZZ\/p^2 ZZ edge("<-")
    & dots.c.h edge("<-")
    & ZZ\/p^n ZZ edge("<-")
    & dots.c edge("<-")
    & ZZ\/p^m ZZ edge("<-")
    & dots.c
  $)
]

A $p$-adic integer can be represented as a sequence
$ x = (x_1 med mod med p , x_2 med mod med p^2 , x_3 med mod med p^3 , dots.c) $
such that $x_(n + 1) equiv x_n med mod med p^n$ for all
$n in bb(Z)_(gt.eq 1)$. Writing in base-$p$ form, $x_n med mod med p^n$
can be represented as
$ x_n = a_0 + a_1 p + dots.c + a_(n - 1) p^(n - 1) = (thin overline(a_(n - 1) op(dots.h.c) a_1 a_0) thin)_p . $
The condition $x_(n + 1) equiv x_n med mod med p^n$ means that
$x_(n + 1)$ and $x_n$ have the same last $n$ digits in base-$p$ form.
Thus $p$-adic integer $x$ can be thought as a base-$p$ interger with
infinite digits
$ x = a_0 + a_1 p + dots.h.c + a_n p^n + dots.h.c = (thin overline(op(dots.h.c) a_n op(dots.h.c) a_1 a_0) thin)_p . $
The projection map $pi_n : bb(Z)_p arrow.r bb(Z) \/ p^n bb(Z)$ is the
truncation map that truncates the last $n$ digits of $x$ in base-$p$
form.

#definition[$p$-adic Valuation][
  Let $p$ be a prime number. The #strong[$p$-adic valuation] is defined as
  $
    v_p : bb(Q) & arrow.r.long bb(Z) union {oo}\
    a / b & arrow.r.bar.long cases(delim: "{", oo & upright("if ") a = 0 ,, max { n in bb(Z) divides p^n divides a } - max { n in bb(Z) divides p^n divides b } & upright("if ") a eq.not 0 .)
  $
]


The #strong[$p$-adic absolute value] is defined as
$
  lr(|thin dot.op thin|)_p : bb(Q) & arrow.r.long bb(R)_(gt.eq 0)\
  x & arrow.r.bar.long cases(delim: "{", 0 & upright("if ") a = 0 ,, p^(- v_p (x)) & upright("if ") x eq.not 0 .)
$


#definition[Global Field][
  A #strong[global field] is a field isomorphic to one of the following:

  - a #strong[number field];: finite extension of $bb(Q)$,

  - a #strong[function field] over a finite field $bb(F)_q$: finite extension of $bb(F)_q (t)$.
]

#definition[Local Field][
  A #strong[local field] is a field isomorphic to one of the following:

  - (Character zero): $bb(R)$, $bb(C)$ or a finite extension of $bb(Q)_p$,

  - (Character $p > 1$): the field of formal Laurent series
    $bb(F)_q ((t))$, where $q = p^n$.
]

== Dirichlet Charater

#definition[Euler's Totient Function][
  The #strong[Euler’s totient function] is defined as
  $
    phi : bb(N) & arrow.r bb(N)\
    n & arrow.r.bar lr(|{a in bb(N) divides 1 lt.eq a lt.eq n , (a , n) = 1}|) .
  $
]

#proposition[Euler's Product Formula][
  For any $n in bb(N)$, we have
  $ phi (n) = sum_(k = 1)^n bb(1)_((k , n) = 1) = n product_(p divides n) (1 - 1 / p) . $
]

#proposition[Properties of Euler's Totient Function][
  For any $m , n in bb(N)$, we have

  #block[
    #set enum(numbering: "(i)", start: 1)
    + $phi (m n) = phi (m) phi (n)$ if $(m , n) = 1$.

    + $phi (n) divides n$.

    + $phi (n) = n$ if and only if $n = 1$.

    + $phi (p^k) = p^k - p^(k - 1)$ for any prime $p$ and $k in bb(N)$.

    + $phi (n) lt.eq n - sqrt(n)$ for any $n in bb(N)$.
  ]
]


#definition[Dirichlet Character][
  Given any group homomorphism
  $rho_m : (bb(Z) \/ m bb(Z))^times arrow.r bb(C)^times$, we can define a
  function $chi : bb(Z) arrow.r bb(C)$ by
  $
    chi_m (a) =
    cases(0 & upright(" if ") [a] in.not (bb(Z) \/ m bb(Z))^times & upright("i.e. ") (a , m) > 1\
    rho ([a]) & upright(" if ") [a] in (bb(Z) \/ m bb(Z))^times & upright("i.e. ") (a , m) = 1
    )
  $
  Such function $chi_m$ is called a #strong[Dirichlet character modulo
$m$];.
]


#definition[Principal Dirichlet Character][
  The #strong[principal Dirichlet character modulo $m$] is the simplest
  Dirichlet character defined by
  $
    chi_0 (a) = cases(0 & upright(" if ") a eq.not 1\
    1 & upright(" if ") a = 1)
  $
]

