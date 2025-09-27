#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node
#import "@preview/cetz:0.3.4"
#import "@preview/in-dexter:0.7.2" as in-dexter: index
#import "@local/math-notes:0.3.0": *


#show: math_notes.with(
  title: [ELLIPTIC CURVES \
    And MODULAR FORMS],
  theme: "light",
)

#let index_math = index.with(index: "Math")

#let SL = math.op("SL")
#let PSL = math.op("PSL")
#let GL = math.op("GL")
#let Tr = math.op("Tr")

#let Gal = math.op("Gal")
#let Frob = math.op("Frob")

#let pmod(n) = $med (mod med #n)$

#let chargrp(G) = $frak(X)(#G)$
#let algdual(G) = $#G^(or.curly)$

#let rightarrow = $stretch(->, size: #15pt)$

#let leftarrow = $stretch(<-, size: #15pt)$

#let movebase(size, x) = text(baseline: size)[#x]

#let (varprojlim, varinjlim) = (leftarrow, rightarrow).map(arrow => $display(limits(lim_(movebase(#(-1.9pt), arrow))))$)

#let injlim(subscript) = $varinjlim_movebase(#(-2.8pt), subscript)$
#let projlim(subscript) = $varprojlim_movebase(#(-2.8pt), subscript)$

#let xrightarrow = $stretch(->, size: #150%)$



#let cal(x) = math.class("unary", text(font: "Computer Modern Symbol", x))
#let racts = $arrow.ccw.half$

#let mmat(..array) = (
  $
    lr([| #math.mat(delim: none, ..array) |], size: #120%)
  $
)

#let noindent(body) = {
  set par(first-line-indent: 0pt)
  body
}






= Basic Concepts of Elliptic Curves <basic-concepts-of-elliptic-curves>
== Elliptic Curves <elliptic-curves>
#definition[Elliptic Curve][
  An *elliptic curve* is a smooth, projective, algebraic curve of genus one with a distinguished point.
]


=== Long Weierstrass form <long-weierstrass-form>
Affine part $ y^2 + a_1 x y + a_3 y = x^3 + a_2 x^2 + a_4 x + a_6 $

#strong[Discriminant and $j$-invariant] \
Let
$
  b_2 & colon.eq a_1^2 + 4 a_2 \
  b_4 & colon.eq a_1 a_3 + 2 a_4 \
  b_6 & colon.eq a_3^2 + 4 a_6 \
  b_8 & colon.eq a_1^2 a_6 - a_1 a_3 a_4 + a_2 a_3^2 + 4 a_2 a_6 - a_4^2 \
  c_4 & colon.eq b_2^2 - 24 b_4 \
  c_6 & colon.eq - b_2^3 + 36 b_2 b_4 - 216 b_6
$
Then the discriminant is defined as
$
  Delta = - b_2^2 b_8 - 8 b_4^3 - 27 b_6^2 + 9 b_2 b_4 b_6 = frac(c_4^3 - c_6^2, 1728)
$
And the $j$-invariant is defined as $ j = c_4^3 \/ Delta $ Invariant holomorphic differential form (Néron differential)
$
  omega = dif p lr((z)) \/ p^prime lr((z)) = dif z = (dif x) / (2 y + a_1 x + a_3)
$

=== Short Weierstrass form <short-weierstrass-form>
Affine part $ y^2 = x^3 + a x + b $ with determinant $ Delta = - 16 lr((4 a^3 + 27 b^2)) eq.not 0 $ The $j$-invariant is defined as $ j = 1728 frac(4 a^3, 4 a^3 + 27 b^2) $

== Elliptic Integral <elliptic-integral>
=== Legendre form <legendre-form>
$
  y^2 = lr((1 - x^2)) lr((1 - k^2 x^2))
$
Complete elliptic integral of the first kind
$
  K(k)= integral_0^1 (dif x) / sqrt((1-x^2)(1-k^2 x^2))
$

Let $omega = (dif x) / y$, then
$
  integral_(C_1) omega = 4 K lr((k)) ,
$
where $C_1$ is a closed path around from $0$ to $1$ and back to $0$.

=== Carlson symmetric form <carlson-symmetric-form>
$ y^2 = x lr((x + 1 - k^2)) lr((x + 1)) $ Complete elliptic integral of the first kind
$
  K(k)=R_F (0,1-k^2,1)=1 / 2 integral_0^oo (dif x) / sqrt(x(x+1-k^2)(x+1))
$
where $R_F$ is the Carlson symmetric form.

=== Carlson to Legendre <carlson-to-legendre>
Suppose $ E_1 : y^2 & = lr((1 - x^2)) lr((1 - k^2 x^2)) \
E_2 : Y^2 & = X lr((X + 1 - k^2)) lr((X + 1)) $ There is a rational map $ phi.alt : E_1 & --> E_2 \
  lr((x , y)) & arrow.r.long.bar lr((1 / x^2 - 1 , y / x^3)) = lr((X , Y)) $ We can check it by substituting $X = 1 / x^2 - 1$ and $Y = y / x^3$ into $E_2$ $ y^2 / x^6 & = lr((1 / x^2 - 1)) lr((1 / x^2 - k^2)) 1 / x^2 $ Then we can use $phi.alt$ to pullback the integral on $E_2$ to $E_1$
$
  integral_0^infinity (upright(d) X) / sqrt(X(X+1-k^2)(X+1))=integral_0^infinity (upright(d) X) / Y =integral_1^0 (-2\/x^3) / (y\/x^3)upright(d) x=2integral_0^1 (upright(d) x) / y=2 integral_0^1 (upright(d) x) / sqrt((1-x^2)(1-k^2 x^2)).
$

// #pagebreak()


// = Elliptic Curves over $bb(CC)$
// ==

#pagebreak()

= Modular Forms

== Action of $SL_2(ZZ)$ <action-of-SL2>


#lemma[][
  Let $gamma = mat(
    a, b;
    c, d
  ) in GL_2(ℂ)$. Then we have the following equality of differential forms:

  $
    dif(γ z) = det(γ) / (c z + d)^(2) dif z.
  $
]<differential-form-of-mobius-transformation>



#lemma[][
  Let $γ = mat(
    a, b;
    c, d
  ) in GL_2(ℝ)$. Then
  $
    op("Im")(γ z) =det(γ)· (op("Im")(z)) / abs(c z + d)^2 .
  $
]<imaginary-part-of-mobius-transformation>

#proof[
  On the one hand, we have $γ z - overline(γ z) = 2i op("Im")(γ z)$. On the other hand, we have
  $
    γ z - overline(γ z) & =frac(a z + b, c z + d) - frac(a overline(z) + b, c overline(z) + d) \
                        & = frac((a z + b)(c overline(z) + d) - (a overline(z) + d)(c z + d), |c z + d|^2) \
                        & = ((a d - b c)(z - overline(z))) / abs(c z + d)^2 \
                        & = det(γ) ·(2i op("Im")(z)) / abs(c z + d)^2.
  $

]


#proposition[Generators of $SL_2(ZZ)$][
  The group $SL_2(ZZ)$ is generated by the matrices $S=mat(0, -1; 1, 0)$ and $T=mat(1, 1; 0, 1)$.
]
#proof[
  We can check that for any integer $n in ZZ$, we have
  $
    S^2 = mat(-1, 0; 0, -1)=-I,quad T^n = mat(1, n; 0, 1), quad L_n:=S^(-1)T^n S = mat(1, 0; -n, 1).
  $
  Given any matrix $A=mat(a, b; c, d) in SL_2(ZZ)$, we will show that $A$ can be written as a product of $S$ and $T$.

  - If $c = 0$, then we have $a d =1$. When $a=d=1$, we have $A=T^b$. When $a=d=-1$, we have $A=S^2T^(-b)$.

  - If $c eq.not 0$, then there exists $q,r in ZZ$ such that $c=q a + r$ , where $|r|<|a|$. By left multiplying $A$ by $L_q$, we get
    $
      L_q A =mat(1, 0; -q, 1)mat(a, b; c, d)= mat(a, b; c-q a, d-q b) = mat(a, b; r, d-q b) .
    $
    Since $|r|<|a|$, we can repeat this process until we get $r=0$. So it reduces to the first case.
]


=== Action of $SL_2(ZZ)$ on $HH$ <action-of-SL2-on-H>

The fundamental domain of the action of $SL_2(ZZ)$ on $HH$ is the set $cal(D)$ defined by

$
  cal(D) = {tau in HH mid(|) -1 / 2 <= op("Re")(tau) <= 1 / 2, med |tau| >= 1}
$

#cetz_canvas({
  import cetz.draw: *
  scale(200%)
  set-style(stroke: (paint: luma(40%), thickness: 1pt))
  // Your drawing code goes here
  let rho_y = calc.sqrt(3) / 2
  let boundry_color_1 = teal.darken(10%)
  let boundry_color_2 = orange.lighten(10%).desaturate(15%)
  let boundry_point_color = red.darken(5%).desaturate(15%)

  let boundry_stroke_1 = (paint: boundry_color_1, thickness: 2pt)
  let boundry_stroke_2 = (paint: boundry_color_2, thickness: 2pt)

  get-ctx(ctx => {
    let background_color = ctx.background
    let luma = background_color.luma().components(alpha: false).at(0)

    let region_color = gradient.linear(background_color.desaturate(10%), aqua.desaturate(80%), angle: 90deg)

    rect((-0.5, 0), (0.5, 2.299), fill: region_color, stroke: none) // region

    line((0.5, 0), (0.5, rho_y))

    arc((1, 0), start: 0deg, delta: 180deg, fill: ctx.background)
  })

  arc((60deg, 1), start: 60deg, delta: 60deg, stroke: boundry_stroke_2, mark: (
    symbol: "straight",
    stroke: boundry_stroke_2,
    offset: 12%,
    scale: 0.7,
  )) // mark

  arc((60deg, 1), start: 60deg, delta: 60deg, stroke: boundry_stroke_2)

  line((-1.5, 0), (1.5, 0)) // x-axis


  line((0.5, 0), (0.5, rho_y))
  line((0.5, rho_y), (0.5, 2.3), stroke: boundry_stroke_1)
  mark((0.5, 1.75), (0.5, 1.8), symbol: "straight", stroke: boundry_stroke_1, scale: 0.7)


  line((-0.5, 0), (-0.5, 2.3))
  line((-0.5, rho_y), (-0.5, 2.3), stroke: boundry_stroke_1)
  mark((-0.5, 1.75), (-0.5, 1.8), symbol: "straight", stroke: boundry_stroke_1, scale: 0.7)

  circle((0, 1), radius: .04, fill: boundry_point_color, stroke: none)
  circle((60deg, 1), radius: .04, fill: rgb("#806cd0"), stroke: none)
  circle((120deg, 1), radius: .04, fill: rgb("#806cd0"), stroke: none)

  content((0.5, -0.15), $1 / 2$)
  content((-0.5, -0.15), $-1 / 2$)
  content((1, -0.15), $1$)
  content((-1, -0.15), $-1$)
  content((0, 0.85), $i$)
  content((0.63, 0.97), $rho$)
  content((-0.63, 0.97), $rho^2$)
})

// #{
//   set align(center)
//   v(1em)
//   cetz.canvas(
//     length: 1.2cm,
//     {
//       import cetz.draw: *
//       scale(200%)
//       set-style(stroke: (paint: luma(40%), thickness: 1pt))
//       // Your drawing code goes here
//       let rho_y = calc.sqrt(3) / 2
//       let boundry_color_1 = teal.darken(10%)
//       let boundry_color_2 = orange.lighten(10%).desaturate(15%)
//       let boundry_point_color = red.darken(5%).desaturate(15%)

//       let region_color = gradient.linear(aqua.desaturate(90%), aqua.desaturate(50%), angle: 90deg)

//       let boundry_stroke_1 = (paint: boundry_color_1, thickness: 2pt)
//       let boundry_stroke_2 = (paint: boundry_color_2, thickness: 2pt)


//       rect((-0.5, 0), (0.5, 2.299), fill: region_color, stroke: none) // region


//       line((0.5, 0), (0.5, rho_y))
//       arc((1, 0), start: 0deg, delta: 180deg, fill: white)

//       arc(
//         (60deg, 1),
//         start: 60deg,
//         delta: 60deg,
//         stroke: boundry_stroke_2,
//         mark: (symbol: "straight", stroke: boundry_stroke_2, offset: 12%, scale: 0.7),
//       ) // mark

//       arc((60deg, 1), start: 60deg, delta: 60deg, stroke: boundry_stroke_2)

//       line((-1.5, 0), (1.5, 0)) // x-axis


//       line((0.5, 0), (0.5, rho_y))
//       line((0.5, rho_y), (0.5, 2.3), stroke: boundry_stroke_1)
//       mark((0.5, 1.75), (0.5, 1.8), symbol: "straight", stroke: boundry_stroke_1, scale: 0.7)


//       line((-0.5, 0), (-0.5, 2.3))
//       line((-0.5, rho_y), (-0.5, 2.3), stroke: boundry_stroke_1)
//       mark((-0.5, 1.75), (-0.5, 1.8), symbol: "straight", stroke: boundry_stroke_1, scale: 0.7)

//       circle((0, 1), radius: .04, fill: boundry_point_color, stroke: none)
//       circle((60deg, 1), radius: .04, fill: rgb("#19bf13"), stroke: none)
//       circle((120deg, 1), radius: .04, fill: rgb("#19bf13"), stroke: none)

//       content((0.5, -0.15), $1 / 2$)
//       content((-0.5, -0.15), $-1 / 2$)
//       content((1, -0.15), $1$)
//       content((-1, -0.15), $-1$)
//       content((0, 0.85), $i$)
//       content((0.63, 0.97), $rho$)
//       content((-0.63, 0.97), $rho^2$)
//     },
//   )
// }

#lemma[$SL_2(ZZ)$-Actions in $cal(D)$][
  Let
  $
    cal(D) = {tau in HH mid(|) -1 / 2 <= op("Re")(tau) <= 1 / 2, med |tau| >= 1}.
  $
  Suppose $tau_1$ and $tau_2$ are two distinct points in $cal(D)$. Then there exists $gamma in SL_2(ZZ)$ such that $tau_2 = gamma tau_1$ if and only if one of the following conditions holds:

  + $op("Re")(tau_1)= plus.minus 1 / 2$ and $tau_2 = tau_1 minus.plus 1$.

  + $|tau_1| = 1$ and $tau_2 = -1 / tau_1$.
]
#proof[
  If there exists $gamma = mat(a, b; c, d) in SL_2(ZZ)$ such that $tau_2 = gamma tau_1$, without loss of generality we can assume $op("Im")(tau_2) >= op("Im")(tau_1)$. According to @imaginary-part-of-mobius-transformation, we have
  $
    op("Im")(tau_2) = (op("Im")(tau_1)) / abs(c tau_1 + d)^2 >= op("Im")(tau_1) ==> abs(c tau_1 + d) <= 1.
  $
  Let $tau_1 = x + i y$ where $x,y in RR$. Then we have
  $
    abs(c tau_1 + d) = (c x + d)^2 + c^2 y^2 <=1
  $
  Note that $y >= sqrt(3)/2$. We have $1>=c^2 y^2 >= 3 / 4 c^2$. Since $c in ZZ$, there must be $c in {-1,0,1}$.

  #[
    #set enum(numbering: "(1)")

    + If $c=0$, then $gamma = mat(1, b; 0, 1)$ for some $b in ZZ$. Then we have $tau_2 = tau_1 + b$. So $op("Re")(tau_1)= plus.minus 1 / 2$ and $tau_2 = tau_1 plus.minus 1$.

    + If $c=1$, then we have $abs(tau_1 + d)<=1$ for some $d in ZZ$, which implies that $d in {-1,0,1}$.

      #set enum(numbering: "(a)")
      + If $d=0$, then $|tau_1| = 1$ and $gamma = mat(a, -1; 1, 0)$. Thus we have $tau_2 = a -1 / tau_1 in cal(D)$, which implies $a in {-1, 0, 1}$.

        - If $a=0$, then $tau_2 = -1 / tau_1$.

        - If $a=plus.minus 1$, then $tau_2 = plus.minus 1 / 2 + sqrt(3) / 2 i$. In this case, $tau_1 = tau_2$, which contradicts the assumption that $tau_1$ and $tau_2$ are distinct.

      + If $d=plus.minus 1$, then $gamma= mat(a, b; 1, plus.minus 1)$ and $tau_1 = minus.plus 1 / 2 + sqrt(3) / 2 i$. Note $op("Im")(tau_2)=(op("Im")(tau_1)) / abs(c tau_1 + d)^2 = op("Im")(tau_1)$. This forces $tau_2 = plus.minus 1 / 2 + sqrt(3) / 2 i$. And we have $tau_2 = tau_1 plus.minus 1$.

    + If $c=-1$, replace $gamma$ by $-gamma$ and we can get the same conclusion.
  ]
]

#definition[Elliptic Point][
  Suppose $Gamma$ is a discrete subgroup of $SL_2(RR)$. We say $tau in HH$ is an *elliptic point* of $Gamma$ if one of the following equivalent conditions holds:

  + $tau$ is a fixed point of some elliptic element $gamma in Gamma$.

  + $op("Stab")_(Gamma)(tau) eq.not {op("id")}$.
]
#remark[
  If $tau in HH$ is an elliptic point of $Gamma$, then $tau$ is the unique fixed point of an elliptic element of $Gamma$ under the action of $Gamma arrow.cw.half HH$.

  Since $op("Stab")_(Gamma)(gamma tau)=gamma op("Stab")_(Gamma)(tau)gamma^(-1)$, if $tau$ is an elliptic point of $Gamma$, then all points in the $Gamma$-orbit of $tau$ are also elliptic points of $Gamma$.
]

#proposition[Elliptic Points form a Discrete Subset of $HH$][
  Suppose $Gamma$ is a discrete subgroup of $SL_2(RR)$. The set of elliptic points of $Gamma$ is a discrete subset of $HH$.
]

#proposition[Group Presentation of $PSL_2(ZZ)$][
  The group $PSL_2(ZZ)$ is generated by the matrices $S=mmat(0, -1; 1, 0)$ and $T=mmat(1, 1; 0, 1)$. As Mobius transformations, generators can be described as follows:

  - $S: tau |-> -1 / tau$ is the action that first inverses the point $tau$ with respect to unit circle centered at the origin, and then reflects the point with respect to the imaginary axis $op("Re")(z)=0$.

  - $T: tau |-> tau + 1$ is the action that translates the point $tau$ one unit to the right.

  Moreover, $PSL_2(ZZ)$ has the following group presentation:

  $
    phi :PSL_2(ZZ) & -->^(tilde)angle.l x, y mid(|) x^2 = y^3 = 1 angle.r tilde.equiv C_2 * C_3 \
                 S & mapsto.long x, \
               S T & mapsto.long y.
  $
]


#example[Elliptic Points of $SL_2(ZZ)$][
  The elliptic points of $Gamma(1)=SL_2(ZZ)$ are those $tau in HH$ such that $tau in Gamma(1) i union.sq Gamma(1)rho$, where $rho = 1 / 2 + sqrt(3) / 2 i$. The stabilizer of $i$ and $rho$ in $SL_2(ZZ)$ are given by
  $
    op("Stab")_(SL_2(ZZ))(i) = ⟨S⟩ tilde.equiv op("C")_2, \
    op("Stab")_(SL_2(ZZ))(rho) = ⟨T S⟩ tilde.equiv op("C")_3,
  $
  where $S=mat(0, -1; 1, 0)$ and $T=mat(1, 1; 0, 1)$.
]


=== Action of $SL_2(ZZ)$ on $upright(bold(P))_RR^1=RR union.sq {oo}$ <action-of-SL2-on-H>

#proposition[Stabilizer of $oo$ in $SL_2(ZZ)$ and $PSL_2(ZZ)$][
  $SL_2(ZZ)$ and $PSL_2(ZZ)$ acts on $RR union.sq {oo}$ by Mobius transformations. The stabilizer of $oo$ is given by
  $
    op("Stab")_(SL_2(ZZ))(oo) = { plus.minus
      mat(1, n; 0, 1) mid(|) n in ZZ },quad
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
  It is sufficient to show that for any $(a:c)in upright(bold(P))^1_QQ$, where $a$, $c$ are coprime integers, there exists $gamma in SL_2(ZZ)$ such $gamma oo = (a:c)$. Note that coprimeness guarantees that there exist $b,d in ZZ$ such that $a d - b c = 1$. So take $ gamma=mat(a, b; c, d)in SL_2(ZZ) $ and we have
  $
    gamma oo=mat(a, b; c, d) mat(1; dot dot; 0)=mat(a; dot dot; c).
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
    level $N$* #index("congruence subgroup", "principal") in $upright(S L)_2 (bb(Z))$ is the kernel of $pi_N$,
  and it is usually denoted by
  $
    Gamma (N) = ker pi_N = { mat(a, b; c, d) in upright(S L)_2 (bb(Z)) : mat(delim: "[", a, b; c, d) equiv mat(1, ; , 1) med(mod med N) }.
  $
  #index_math(display: [$Gamma (N)$], "Gamma(N)") where the matrix congruence is interpreted entrywise, i.e.
  $
    a & equiv d & equiv 1 med & (mod med N), \
    b & equiv c & equiv 0 med & (mod med N).
  $

]

#lemma[][
  $pi_N : SL_2 (bb(Z)) --> SL_2 (bb(Z) \/ N bb(Z))$ is surjective. And we have $|SL_2(ZZ): Gamma(N)|=|SL_2 (bb(Z) \/ N bb(Z))|<oo$.
]
#proof[
  For any matrix $B=mat(overline(a), overline(b); overline(c), overline(d)) in SL_2 (bb(Z) \/ N bb(Z))$, we need to find a matrix $A=mat(a', b'; c', d') in SL_2 (bb(Z))$ such that $pi_N (A)=B$. That is, find integers $a',b',c',d' in ZZ$ such that $a' equiv a med (mod med N)$, $b' equiv b med (mod med N)$, $c' equiv c med (mod med N)$, $d' equiv d med (mod med N)$ and $a' d' - b' c' = 1$.
  - First we are to find $a',b' in ZZ$ such that $gcd(a', b')=1$ and $a' d - b' c equiv 1 med (mod med N)$. Suppose $a eq.not 0$. According to Chinese remainder theorem, there exists an integer $t$ such that
    $
      t equiv cases(
        1 quad & ( mod med p)\, &                        quad forall"prime" p divides gcd (a , b) \
        0 quad & ( mod med p)\, & quad forall"prime" p divides.not gcd (a , b) \, med p divides a
      )
    $
    Let $a'=a$, $b'=b+t N$. Then $a' d - b' c equiv 1 med (mod med N)$. Assume that $p$ is any prime factor of $a$.

    + If $p$ is also a prime factor of $b$, then #h(1fr)
      $
        b' equiv b+t N equiv N med (mod med p).
      $
      Note that
      $
        a d-b c equiv 1 med (mod med N)==>gcd(a, b, N)=1.
      $
      $p divides gcd(a, b)$ means $p$ is not a prime factor of $N$. So we have $p divides.not b'$.
    + If $p$ is not a prime factor of $b$, then #h(1fr)
      $
        b' equiv b+t N equiv b med (mod med p).
      $
      So again we have $p divides.not b'$.

    Thus we show that $gcd(a', b')=1$.

  - Then we construct $c'$ and $d'$. Suppose $a' d-b' c=1+k N$, where $k in ZZ$. It is sufficient to show that there exist $x,y in ZZ$ such that $c'=c+x N$, and $d'=d+y N$ and $a' d' - b' c' = 1$.
    Note that
    $
      a' d' - b' c' = 1 <==> a'(d+y N)-b'(c+x N)=a'd-b'c-k N <==>b'x-a'y=k.
    $
    Since $gcd(a', b')=1$ divides $k$, there exist integer solution $x^*,y^*$ such that $b'x^*-a'y^*=k$, which completes the proof.
]

#definition[Congruence Subgroup of $SL_2(ZZ)$][
  A subgroup $Gamma$ of $SL_2(ZZ)$ is called a *congruence subgroup* #index("congruence subgroup") if it contains $Gamma(N)$ for some positive integer $N$.
]
#proposition[Properties of Congruence Subgroups][
  Let $Gamma$ be a congruence subgroup of $SL_2(ZZ)$.

  - $Gamma$ is a discrete subgroup of $SL_2(RR)$.

  - The index $abs(SL_2(ZZ):Gamma)$ is finite.
]
#proof[
  - It is clear that $upright(M)_2(ZZ)$ is a discrete subspace of $upright(M)_2(RR)$. Since any subspace of a discrete space is discrete, any concruence subgroup is discrete in $upright(M)_2(RR)$.
  - Suppose $Gamma$ has a subgroup $Gamma(N)$. Since $pi_N : SL_2 (bb(Z)) ->> SL_2 (bb(Z) \/ N bb(Z))$ is surjective, we have $abs(SL_2(ZZ):Gamma(N))=abs(im pi_N)= abs(SL_2 (bb(Z) \/ N bb(Z)))<oo$. From
    $
      abs(SL_2(ZZ):Gamma) med abs(Gamma : Gamma(N))=abs(SL_2(ZZ):Gamma(N))
    $
    we see both $abs(SL_2(ZZ):Gamma)$ and $abs(Gamma :Gamma(N))$ are finite.
]


#example[Congruence Subgroups $Gamma_1(N)$][
  Let $N$ be a positive integer. Define $P$ to be the subgroup of $SL_2(ZZ\/N ZZ)$ consisting of unipotent upper triangular matrices. For each $N$, #index_math(display: [$Gamma_1 (N)$], "Gamma_1(N)")
  $
    Gamma_1 (N) = pi_N^(-1)(P) = { mat(a, b; c, d) in upright(S L)_2 (bb(Z)) : mat(delim: "[", a, b; c, d) equiv mat(1, *; , 1) med(mod med N) }
  $
  is a congruence subgroup of $SL_2(ZZ)$. We can check that
  $
    op("pr")_(12): Gamma_1 (N) & --> bb(Z)\/N bb(Z), \
               mat(a, b; c, d) & arrow.long.bar b med(mod med N).
  $
  is a surjective group homomorphism and we have the exact sequence
  $
    1 --> Gamma (N) --> Gamma_1 (N) -->^(op("pr")_12) bb(Z)\/N bb(Z) --> 1.
  $
  Therefore, $[Gamma_1 (N): Gamma (N)] = N$.
]
#proof[
  First we show that $op("pr")_(12)$ is a group homomorphism.
  $
    op("pr")_12 ( mat(a_1, b_1; c_1, d_1) mat(a_2, b_2; c_2, d_2) ) = a_1 b_2 + b_1 d_2 med(mod med N) equiv b_1+ b_2 med(mod med N)
  $
  implies
  $
    op("pr")_12 (mat(a_1, b_1; c_1, d_1) mat(a_2, b_2; c_2, d_2)) = op("pr")_12 (mat(a_1, b_1; c_1, d_1)) +op("pr")_12 ( mat(a_2, b_2; c_2, d_2) ).
  $
  Then we see $p_(12)$ is surjective because for any $b in bb(Z)\/N bb(Z)$, we can find $mat(1, b; 0, 1) in Gamma_1 (N)$ such that
  $
    op("pr")_12 (mat(1, b; , 1)) = b.
  $
  Finally we check the kernel of $op("pr")_(12)$ is
  $
    ker op("pr")_(12) = {mat(a, b; c, d) in Gamma_1 (N) : b equiv 0 med(mod med N)} = Gamma (N).
  $
]


#example[Hecke Congruence Subgroups $Gamma_0(N)$][
  Let $N$ be a positive integer. Define $SL_2^◹(ZZ\/N ZZ)$ to be the subgroup of $SL_2(ZZ\/N ZZ)$ consisting of upper triangular matrices. The *Hecke congruence subgroup of level $N$* is defined as #index_math(display: [$Gamma_0 (N)$], "Gamma_0(N)")
  $
    Gamma_0 (N) = pi_N^(-1)(SL_2^◹(ZZ\/N ZZ)) = { mat(a, b; c, d) in upright(S L)_2 (bb(Z)) : mat(delim: "[", a, b; c, d) equiv mat(*, *; , *) med(mod med N) }.
  $
]

#proposition[][
  + $
      Gamma (N) subset.eq Gamma_1 (N) subset.eq Gamma_0 (N) subset.eq upright(S L)_2 (bb(Z)).
    $

  + If $N | M$, then $Gamma (M) subset.eq Gamma (N)$.
]

#definition[Cusp of a Congruence Subgroup][
  Let $Gamma$ be a congruence subgroup of $SL_2(ZZ)$. Then $Gamma$ acts on $QQ union.sq {oo}$ through Mobius transformations. A *cusp* of $Gamma$ is a $Gamma$-orbit in $upright(bold(P))^1_QQ=QQ union.sq {oo}$. #index_math(display: [$upright(bold(P))^1_QQ$], "P^1(Q)")
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
  For any $gamma = mat(a, b; c, d) in upright("GL")_2 (bb(C))$, the *factor of automorphy* of $gamma$ is defined as #index_math(display: [$j(gamma, tau)$], "j(gamma, tau)")
  $
    j(gamma, tau) = c tau + d, quad tau in bb(H).
  $
]

#lemma[Properties of Factor of Automorphy][
  - For any $gamma_1,gamma_2 in upright("GL")_2 (bb(R))^+$, we have
  $
    j(gamma_1 gamma_2, tau) = j(gamma_1, gamma_2 tau) j(gamma_2, tau), quad tau in bb(H).
  $
  - For any $gamma = mat(cos theta, - sin theta; sin theta, cos theta) in op("SO")_2 (bb(R))$, we have
  $
    j(gamma, i) = e^(i theta)=cos theta + i sin theta.
  $
]<properties-of-factor-of-automorphy>
#proof[
  Note that for any $gamma = mat(a, b; c, d) in upright("GL")_2 (bb(R))^+$, we have

  $
    gamma mat(tau; 1) =mat(a, b; c, d) mat(tau; 1)= mat(a tau + b; c tau + d) = j(gamma, tau) mat(gamma tau; 1).
  $
  On the one hand, we have
  $
    gamma_1 gamma_2 mat(tau; 1) = j(gamma_1 gamma_2, tau) mat(gamma_1 gamma_2 tau; 1) ,
  $
  and on the other hand, we have
  $
    gamma_1 gamma_2 mat(tau; 1) = gamma_1 j(gamma_2, tau) mat(gamma_2 tau; 1) =
    j(gamma_2, tau) gamma_1 mat(gamma_2 tau; 1) = j(gamma_2, tau) j(gamma_1, gamma_2 tau) mat(gamma_1 gamma_2 tau; 1).
  $
  That completes the proof of the first property. The second property is a direct computation.
]

#definition[Weight-$k$ Operator][
  For any integer $k in ZZ$, and $gamma in op("GL")_2(RR)^+$, the *weight-$k$ operator* is defined as
  $
    [gamma]_k : op("Hom")_(sans("Set")) (HH, CC) & --> op("Hom")_(sans("Set")) (HH, CC) \
                                               f & mapsto.long f[gamma]_k
  $
  where
  $
    (f[gamma]_k)(tau) = (det gamma)^(k / 2) j (gamma , tau)^(- k) f (gamma tau) = (det gamma)^(k / 2) ( c tau + d )^(-k) f(gamma tau).
  $
  Specially, for $gamma in upright(S L)_2 (bb(Z))$,
  $
    (f[gamma]_k)(tau) = j (gamma , tau)^(- k) f (gamma tau) = (c tau + d)^(-k) f(gamma tau).
  $
]

#proposition[][
  $op("GL")_2(RR)^+$ acts on $op("Hom")_(sans("Set")) (HH, CC)$ on the right by
  $
    op("Hom")_(sans("Set")) (HH, CC) times op("GL")_2(RR)^+ & --> op("Hom")_(sans("Set")) (HH, CC) \
                                                 (f, gamma) & mapsto.long f[gamma]_k
  $
]
#proof[
  For any $f in op("Hom")_(sans("Set")) (HH, CC)$ and $gamma_1, gamma_2 in op("GL")_2(RR)^+$, by @properties-of-factor-of-automorphy we have
  $
    (f[gamma_1 gamma_2]_k)(tau)& = (det gamma_1 gamma_2)^(k / 2) j(gamma_1 gamma_2, tau)^(-k) f(gamma_1 gamma_2 tau)\
    & = (det gamma_1 gamma_2)^(k / 2) j(gamma_1 ,gamma_2 tau)^(-k) j(gamma_2 , tau)^(-k) f(gamma_1 gamma_2 tau)\
    & = (det gamma_2)^(k / 2) j(gamma_2,tau)^(-k)( (det gamma_1)^(k / 2) j(gamma_1, gamma_2 tau)^(-k)f(gamma_1 gamma_2 tau) )\
    & = (det gamma_2)^(k / 2) j(gamma_2,tau)^(-k)(f[gamma_1]_k)(gamma_2 tau)\
    &= ((f[gamma_1]_k)[gamma_2]_k)(tau).
  $
]

For $N in ZZ_(>=1)$, we have a surjective holomorphic complex Lie group homomorphism
$
  q_N: bb(C) & --> bb(C)^* = {z in CC mid(|) z eq.not 0} \
         tau & mapsto.long e^((2 pi i tau) / N).
$
The kernel of $q_N$ is the subgroup of $H$ given by
$
  ker q_N = {tau in bb(H) mid(|) e^((2 pi i tau) / N ) = 1} = N bb(Z).
$
By restricting $q_N$ to the upper half plane $bb(H)$, we get a surjective holomorphic semigroup homomorphism
$
  q_N: bb(H) & --> bb(D)^*={z in CC mid(|) 0<|z|<1} \
         tau & mapsto.long e^((2 pi i tau) / N ).
$
And we have
$
  q_N(tau_1) = q_N(tau_2) <==> tau_1 equiv tau_2 med(mod med N) <==> tau_1 - tau_2 in N bb(Z).
$
$q_N$ has the following universal property: for any holomorphic function $f: bb(H) --> bb(C)$ such that $f(tau + N) = f(tau)$, there exists a unique holomorphic function $tilde(f): bb(D)^* --> bb(C)$ such that $f = tilde(f) circle.tiny q_N$.

#commutative_diagram(
  $
        HH edge("d", "->>", q_N) edge(->, f) & CC \
    DD^* edge("ru", "-->", tilde(f), #right)
  $,
)

#noindent[This motivates the following definition.]

#definition[$q$-expansion of $N ZZ$-periodic Function][
  Let $N in ZZ_(>=1)$ and $f: bb(H) --> bb(C)$ be a holomorphic function such that $f(tau + N) = f(tau)$. Suppose $f = tilde(f) circle.tiny q_N$ and $tilde(f)$ has Laurent expansion $tilde(f)(q)=limits(sum)_(n in ZZ) a_n q^n$. Then $f$ can be written as
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
If $f: bb(H) --> bb(C)$ is a $N ZZ$-periodic holomorphic function, then for any $d in ZZ_(>=1)$, $f$ is also a $d N ZZ$-periodic holomorphic function and we have $q_N=q_(d N)^d$
. The $q$-expansion of $f$ with respect to $q_(d N)$ is given by
$
  f( q ) = sum_(n in ZZ) a_n q^n_(N)= sum_(n in ZZ) a_n e^((2 pi i n tau) / (N))= sum_(n in ZZ) a_n q^(d n)_(d N) = sum_(n in ZZ) a_n e^((2 pi i d n tau) / (d N)).
$

#lemma[$f: bb(H) -> bb(C)$ is Fixed by ${[gamma]_k mid(|)gamma in Gamma}$ Implies $f[alpha]_k$ is $N ZZ$-periodic][
  Suppose $Gamma$ is a congruence subgroup of level $N$ and $f: bb(H) -> bb(C)$ is a function. Consider the right action $op("Hom")_(sans("Set")) (HH, CC) racts op("GL")_2(RR)^+$ given by weight-$k$ operator $f dot gamma = f[gamma]_k$. If $Gamma subset.eq op("Stab")_(op("GL")_2(RR)^+)(f)$, then for any $alpha in SL_2(ZZ)$,
  $
    mat(1, N; , 1) in op("Stab")_(op("GL")_2(RR)^+)(f[alpha]_k),
  $
  or equivalently,
  $
    (f[alpha]_k) (tau+N)=(f[alpha]_k) (tau).
  $
]<f-is-fixed-by-gamma-implies-f-alpha-is-N-periodic>
#proof[
  Note that $Gamma(N)triangle.small.l SL_2(ZZ)$. For any $alpha in SL_2(ZZ)$, we have
  $
    alpha mat(1, N; , 1) alpha^(-1)in alpha Gamma(N) alpha^(-1)=Gamma(N)subset.eq Gamma subset.eq op("Stab")_(op("GL")_2( RR )^+)(f),
  $
  which implies
  $
    mat(1, N; , 1) in alpha^(-1) op("Stab")_(op("GL")_2(RR)^+)(f) alpha=op("Stab")_(op("GL")_2(RR)^+)(f[alpha]_k).
  $
]
#definition[Meromorphicity at Cusps][
  Let $Gamma$ be a congruence subgroup of level $N$ and $f: bb(H) -> bb(C)$ be a holomorphic function. Consider the right action $op("Hom")_(sans("Set")) (HH, CC) racts op("GL")_2(RR)^+$ given by weight-$k$ operator $f dot gamma = f[gamma]_k$. Suppose $Gamma subset.eq op("Stab")_(op("GL")_2(RR)^+)(f)$ and $x=alpha oo$ for some $alpha in SL_2(ZZ)$.
  Then we say

  - $f$ is *meromorphic at $Gamma x in Gamma\\ upright(bold(P))^1_QQ$* if $f[alpha]_k$ is meromorphic at $oo$.

  - $f$ is *holomorphic at $Gamma x in Gamma\\ upright(bold(P))^1_QQ$* if $f[alpha]_k$ is holomorphic at $oo$.

  - $f$ *vanishes at $Gamma x in Gamma\\ upright(bold(P))^1_QQ$* if $f[alpha]_k$ vanishes at $oo$.

]

#remark[
  We should check meromorphicity at a cusp is a well-defined property. First, we show that the meromorphicity of $f$ at $x in upright(bold(P))^1_QQ$ is well-defined. That is, if there exist $alpha,beta in op("SL")_2(ZZ)$ such that $alpha oo = beta oo$, then the meromorphicity of $f[alpha]_k$ and $f[beta]_k$ at $oo$ are equivalent. Consider $eta :=alpha^(-1)
  beta in op("Stab")_(op("SL")_2(ZZ))(oo)$. Then $eta$ can be written as $ eta = plus.minus mat(1, m; , 1) $ for some $m in ZZ$ and we have
  $
    f[beta]_k (tau) = f[alpha eta]_k (tau)= (plus.minus 1)^(-k) f[alpha]_k (tau +m) .
  $
  From @f-is-fixed-by-gamma-implies-f-alpha-is-N-periodic, we know both $f[alpha]_k$ and $f[beta]_k$ are $N ZZ$-periodic and have $q$-expansions
  $
    f[alpha]_k (tau) = sum_(n in ZZ) a_n e^((2 pi i n tau) / N),quad f[beta]_k ( tau ) = sum_(n in ZZ) b_n e^((2 pi i n tau) / N).
  $
  Since
  $
    f[beta]_k (tau) = sum_(n in ZZ) b_n e^((2 pi i n tau) / N)= (plus.minus 1)^(-k) f[alpha]_k (tau +m) =( plus.minus 1 )^(-k)sum_(n in ZZ) a_n e^((2 pi i n ( tau
      +m )) / N),
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

  + #emph[Growth condition]: $f$ is holomorphic at all cusps. That is, for any cusp $Gamma x in Gamma\\ upright(bold(P))^1_QQ$, there exists $alpha in op("SL")_2(ZZ)$ such $x = alpha oo$ and $f[alpha]_k$ is holomorphic at $oo$.

  All modular forms of weight $k$ and level $Gamma$
  form a $CC$-vector space, denoted by $M_k (Gamma)$. If $f$ is a modular form of level $Gamma(N)$, then $f$ is called a *modular form of level $N$*. #index("modular form")
]

#definition[Cuspidal Form][
  A modular form $f$ of weight $k$ and level $Gamma$ is called a *cuspidal form* #index("cuspidal form") if $f$ vanishes at all cusps. The space of cuspidal forms of weight $k$ and level $Gamma$ is denoted by $S_k (Gamma)$.
]

#proposition[Graded $CC$-algebra $M(Gamma)$][
  Define #index_math(display: [$M_k (Gamma)$], "M_k(Gamma)")
  $
    M(Gamma) := plus.big_(k in ZZ) M_k (Gamma).
  $
  #index_math(display: [$M(Gamma)$], "M(Gamma)") as the direct sum of $CC$-vector spaces. Then $M(Gamma)$ is a graded $CC$-algebra where the multiplication is given by the multiplication of modular forms. #index_math(display: [$S_k (Gamma)$], "S_k(Gamma)")
  $
    S(Gamma) := plus.big_(k in ZZ) S_k (Gamma)
  $
  #index_math(display: [$S(Gamma)$], "S(Gamma)")is a graded ideal of $M(Gamma)$.
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

= Linear Representations of Groups <representation-theory>
#[
  #set par(first-line-indent: 0pt)
  This chapter is about the linear representation theory of groups.
]
== Representations of Groups

=== Basic Concepts

#definition[Linear Representation of a Group][
  $typebadge(
    G, Grp;
    bb(k), Fld;
    V, Vect(bb(k))
  )$

  A *linear representation* of a group $G$ has the following equivalent definitions:

  + A *linear representation* of $G$ is a group homomorphism
    $
      rho: G & --> GL(V) \
           g & --> rho_g
    $
    for some $bb(k)$-vector space $V$. (The infomation of $V$ is part of the data of $rho$.)

  + A *linear representation* of $G$ is a $bb(k)[G]$-module $M$.

  + A *linear representation* of $G$ is a functor $R: sans(upright("B")) G -> Vect(bb(k))$.
]
#remark[
  Let's show (i) and (ii) are equivalent. Suppose $rho: G -> GL(V)$ is a linear representation of $G$. Then we can define a $bb(k)[G]$-module structure on $V$ by
  $
    g dot v = rho_g (v), quad forall g in G, v in V.
  $
  Conversely, suppose $M$ is a $bb(k)[G]$-module. Then $M$ is also a $bb(k)$-vector space and we can define a group homomorphism $rho: G -> GL(M)$ by

  $
    g arrow.long.bar (rho_(g): v arrow.long.bar g dot v, quad forall v in M).
  $
  It is straightforward to check that this is a bijective correspondence between linear representations of $G$ defined in (i) and $bb(k)[G]$-modules.
]

#definition[Morphisms of Linear Representations][
  $typebadge(
    G, Grp;
    bb(k), Fld;
    V\, W, Vect(bb(k))
  )$

  The morphisms of linear representations of a group $G$ can be defined in the following equivalent ways:

  + Equivariant maps: A morphism of linear representations $f: (V, rho) -> (W, sigma)$ is a linear map $f: V -> W$ such that
    $
      f(g dot v) = g dot f(v), quad forall g in G, forall v in V.
    $
    which is equivalent to saying that for any $g in G$, the following diagram commutes

    #commutative_diagram(
      $
        V edge("d", "->", f) edge(->, rho_g) & V edge("d", "->", f) \
          W edge("r", "->", sigma_g, #right) & W
      $,
    )

  + Module homomorphisms: A morphism of linear representations $f: M -> N$ is a $bb(k)[G]$-module homomorphism. That is, $f$ is a linear map such that
    $
      f(g dot v+w) = g dot f(v)+f(w), quad forall g in G,forall v,w in M.
    $

  + Natural transformations: A morphism of linear representations $f: R_1 => R_2$ is a natural transformation between functors $R_1, R_2: sans(upright("B")) G -> Vect(bb(k))$.
]

#definition[Category of Linear Representations][
  $typebadge(
    G, Grp;
    bb(k), Fld;
  )$

  The category of $bb(k)$-linear representations of a group $G$ is denoted by
  $
    sans("Rep")_bb(k)(G):= [sans(upright("B")) G, Vect(bb(k))] tilde.equiv Mod(bb(k)[G]).
  $
  #index_math(display: [$sans("Rep")_bb(k)(G)$], "Rep_k(G)")
]

#definition[Isomorphism of Linear Representations][
  $typebadge(
    G, Grp;
    bb(k), Fld;
    V\, W, Mod(bb(k)[G])
  )$

  Two linear representations $rho: G -> GL(V)$ and $sigma: G -> GL(W)$ are called *isomorphic* if there exists a linear isomorphism $f: V ->^(tilde) W$ such that
  $
    f circle.tiny rho_g = sigma_g compose f, quad forall g in G.
  $
]

#definition[Trivial Representation][
  $typebadge(
    G, Grp;
    bb(k), Fld;
  )$

  The *trivial representation* of a group $G$ is the linear representation $rho: G -> GL(bb(k))$ such that $rho_g = op("id")_V$ for all $g in G$.
]

#definition[$G$-invariant Subspace][
  $typebadge(
    G, Grp;
    bb(k), Fld;
    V\, W, Mod(bb(k)[G])
  )$

  Let $rho: G -> GL(V)$ be a linear representation of a group $G$. A subspace $W subset.eq V$ is called *$G$-invariant* if
  $
    rho_g (W) subset.eq W, quad forall g in G.
  $
]

#definition[Subrepresentation][
  $typebadge(
    G, Grp;
    bb(k), Fld;
    V\, W, Mod(bb(k)[G])
  )$

  Let $rho: G &-> GL(V)$ be a linear representation of a group $G$. If $W$ is a $G$-invariant subspace of $V$, then we can define a linear representation $rho|_W: G -> GL(W)$ as follows
  $
    rho|_W: G & --> GL(W) \
            g & --> rho_g|_W.
  $
  We call $rho|_W$ a *subrepresentation* of $rho$.
]
#remark[
  From the viewpoint of $bb(k)[G]$-modules, a subrepresentation of a $bb(k)[G]$-module $V$ is a $bb(k)[G]$-submodule $W$ of $V$.
]
#definition[Proper Subrepresentation][
  $typebadge(
    G, Grp;
    bb(k), Fld;
    V\, W, Mod(bb(k)[G])
  )$

  A subrepresentation $W$ of a linear representation $rho: G -> GL(V)$ is called *proper* if $W eq.not V$.
]



#definition[Irreducible Representation][
  $typebadge(
    G, Grp;
    bb(k), Fld;
    V, Mod(bb(k)[G])
  )$

  A linear representation $rho: G -> GL(V)$ is called *irreducible* if $V$ has no proper nontrivial subrepresentations. A linear representation is called *reducible* if it is not irreducible.
]
#remark[
  From the viewpoint of $bb(k)[G]$-modules, an irreducible representation of a group $G$ is a simple $bb(k)[G]$-module.
]

#lemma[Kernal and Image of a $G$-equivariant Map are $G$-invariant][
  $typebadge(
    G, Grp;
    bb(k), Fld;
    V\, W, Mod(bb(k)[G])
  )$

  Let $rho: G -> GL(V)$ and $sigma: G -> GL(W)$ be two linear representations of a group $G$. Suppose $f: V -> W$ is a $G$-equivariant map. Then

  + $ker f$ is a $G$-invariant subspace of $V$.

  + $im f$ is a $G$-invariant subspace of $W$.
]<kernel-and-image-of-equivariant-map-are-invariant>
#proof[
  + Given any $v in ker f$, for any $g in G$, we have #h(1fr)
    $
      f circle.tiny rho_g (v) = sigma_g circle.tiny f (v) = 0 ==> rho_g (v) in ker f,
    $
    which means $ker f$ is a $G$-invariant subspace of $V$.

  + Given any $w=f(v) in im f$, for any $g in G$, we have
    $
      sigma_g (w) = sigma_g compose f(v) = f circle.tiny rho_g (v) in im f,
    $
    which means $im f$ is a $G$-invariant subspace of $W$.
]
#theorem[Schur's Lemma][
  $typebadge(
    G, Grp;
    bb(k), Fld;
    V\, W, Mod(bb(k)[G])
  )$

  Let $rho: G -> GL(V)$ and $sigma: G -> GL(W)$ be two irreducible linear representations of a group $G$. Suppose $f: V -> W$ is a $G$-equivariant map. We have

  + Either $f$ is an isomorphism, or $f=0$.

  + If $V$ is a finite-dimensional vector space over an algebraically closed field $bb(k)$ and $W=V$, then $f=lambda op("id")_V$ for some $lambda in bb(k)$.

  + If $V$ and $W$ are finite-dimensional vector spaces over an algebraically closed field $bb(k)$, then
    $
      dim_bb(k) op("Hom")_(Mod(bb(k)[G])) (V, W) = cases(
        1 & " if" dim_bb(k) V = dim_bb(k) W,
        0 & " if" dim_bb(k) V eq.not dim_bb(k) W
      )
    $
]
#proof[
  + Suppose $f eq.not 0$. This implies $ker f eq.not V$ and $im f eq.not {0}$. According to @kernel-and-image-of-equivariant-map-are-invariant, $ker f$ and $im f$ are $G$-invariant. Since $rho$ and $sigma$ are irreducible, $G$-invariant subspaces of $V$ and $W$ are either entire space or $0$. Therefore, we have $ker f = {0}$ and $im f = W$, which implies $f$ is an isomorphism.

  + Suppose $V$ is a finite-dimensional vector space over an algebraically closed field $bb(k)$ and $W=V$. Since $bb(k)$ is algebraically closed, there exists an eigenvalue $lambda in bb(k)$ such that
    $
      ker(lambda op("id")_V -f) eq.not {0}.
    $
    Since $lambda op("id")_V -f$ is a $G$-equivariant map, according to @kernel-and-image-of-equivariant-map-are-invariant, we see $ker(lambda op("id")_V -f)$ is a $G$-invariant subspace of $V$. Since $V$ is irreducible, we have $ker(lambda op("id")_V -f) = V$, which implies $lambda op("id")_V -f=0$ and $f=lambda op("id")_V$.
]

=== Basic Construction
#definition[Direct Sum of Linear Representations][
  Let $rho: G -> GL(V)$ and $sigma: G -> GL(W)$ be two linear representations of a group $G$. The *direct sum* of $rho$ and $sigma$ is the linear representation $rho plus.circle sigma: G -> GL(V plus.circle W)$ defined by
  $
    (rho plus.circle sigma)_g (v plus.circle w) = rho_g (v) plus.circle sigma_g (w), quad forall g in G, forall v in V, forall w in W.
  $
]

== Finite Dimensional Representations
#definition[Finite Dimensional Representation][
  A linear representation $rho: G -> GL(V)$ is called *finite dimensional* if $V$ is a finite dimensional $bb(k)$-vector space.
]

#remark[
  A finite dimensional representation of a group $G$ is equivalent to a functor $R: sans(upright("B")) G -> FinVect(bb(k))$.
]

#proposition[][
  A nonzero finite-dimensional representation always contains a nonzero irreducible subrepresentation.
]

=== Charater Theory
#definition[Character of a Representation][
  $typebadge(
    G, Grp;
    bb(k), Fld;
    V, FinVect(bb(k))
  )$

  Let $V$ be a finite-dimensional vector space over $bb(k)$ and $rho: G -> GL(V)$ be a linear representation of a group $G$. The *character* of $rho$ is the function $chi_rho: G -> bb(k)$ defined by
  $
    chi_rho (g) = Tr(rho_g), quad forall g in G.
  $
]

#definition[Degree of a Character][
  $typebadge(
    G, Grp;
    bb(k), Fld;
    V, FinVect(bb(k))
  )$

  Let $rho: G -> GL(V)$ be a finite-dimensional representation and $chi_rho$ be the character of $rho$. The *degree* of $chi_rho$ is the dimension of the vector space $V$.

]

#definition[Class Function][
  $typebadge(
    G, Grp;
    bb(k), Fld;
  )$

  A function $f: G -> bb(k)$ is called a *class function* if it is constant on each conjugacy class of $G$. The set of all class functions of $G$ is a $bb(k)$-vector space.
]

#proposition[Class Function Form the Center of $bb(k)[G]$][
  $typebadge(
    G, FinGrp;
    bb(k), Fld;
  )$

  If $G$ is a finite group. Then a class function $f: G -> bb(k)$ can be viewed as an element
  $
    sum_(g in G) f(g) g.
  $
  The set of all class functions of $G$ is precisely the center of $bb(k)[G]$.
]
#proof[
  Suppose $f: G -> bb(k)$ is a function. If $f$ is a class function, then for any $h in G$, we have
  $
    (sum_(g in G) f(g) g)h = sum_(g in G) f(h g h^(-1)) h g h^(-1) h= sum_(g in G) f(g) h g =h(sum_(g in G) f(g) g),
  $
  which implies $limits(sum)_(g in G) f(g) g in Z(bb(k)[G])$.

  Conversely, if $limits(sum)_(g in G) f(g) g in Z(bb(k)[G])$, then for any $h in G$, we have
  $
    sum_(g in G) f(g) g = h (sum_(g in G) f(g) g)h^(-1) = sum_(g in G) f(g) h g h^(-1)= sum_(g in G) f(h^(-1) g h) g ==> f(g) = f(h^(-1) g h),
  $
  which implies $f$ is a class function.

]

#definition[Irreducible Character][
  $typebadge(
    G, Grp;
    bb(k), Fld;
    V, FinVect(bb(k))
  )$

  The character $chi_rho$ of a linear representation $rho: G -> GL(V)$ is called an *irreducible character* if $rho$ is an irreducible representation.
]

#proposition[Properties of Characters][
  $typebadge(
    G, Grp;
    bb(k), Fld;
    V, FinVect(bb(k))
  )$

  Let $V$ be a $n$-dimensional vector space over $bb(k)$ and $rho: G -> GL(V)$ be a representation. Then the character $chi_rho$ of $rho$ has the following properties:

  + $chi_rho$ is a class function. The set of irreducible characters of $G$ forms a basis of the $bb(k)$-vector space of class functions of $G$.

  + Isomorphic representations have the same characters.
]

#proposition[Properties of Characters over Field of Characteristic 0][
  $typebadge(
    G, Grp;
    bb(k), Fld_0;
    V, FinVect(bb(k))
  )$

  Let $V$ be a $n$-dimensional vector space over $bb(k)$ and $rho: G -> GL(V)$ be a representation. Suppose $bb(k)$ has characteristic $0$. Then the character $chi_rho$ of $rho$ has the following properties:

  + Two representations are isomorphic if and only if they have the same character.

  + $chi(1)=n$.
]



#pagebreak()

= Representations of Finite Groups
#[
  #set par(first-line-indent: 0pt)
  This chapter is devoted to the study of linear representations of finite groups.
]

== Finite Dimensional Representations
In this section we focus on the finite-dimensional representations of finite groups.

Recall a linear map $p:V->V$ is called a projection if $p^2=p$. If $p:V->V$ is a projection, then $V=im p plus.circle ker p$.



#lemma[][
  $typebadge(
    bb(k), Fld;
    G, FinGrp;
    V, FinVect(bb(k))
  )$

  Let $rho: G -> GL(V)$ be a representation. Suppose $op("char")(bb(k))$ does not divide $|G|$. If $W$ is a $G$-invariant subspace of $V$, then there exists a complement $W^0$ of $W$ in $V$ such that $V = W plus.circle W^0$ and $W^0$ is also $G$-invariant.
]<complement-of-invariant-subspace>
#proof[
  Let $W'$ be an arbitrary complement of $W$ in $V$. Then $V = W plus.circle W'$. Let $op("pr")_W: W plus.circle W' -> W$ be the projection onto $W$. Define
  $
    op("pr")_W^0 = 1 / abs(G) sum_(g in G) rho_g circle.tiny op("pr")_W circle.tiny rho_g^(-1) .
  $
  Since $im op("pr")_W =W$ and $W$ is $G$-invariant, we see $im op("pr")_W^0 subset.eq W$ and $op("pr")_W^0|_W = op("id")_W$. Therefore, $op("pr")_W^0$ is a projection onto $W$. Let $W^0 = ker op("pr")_W^0$. We have $V = W plus.circle W^0$. For any $h in G$, we can check that
  $
    rho_h circle.tiny op("pr")_W^0 circle.tiny rho_h^(-1) = 1 / abs(G) sum_(g in G) rho_h circle.tiny rho_g circle.tiny op("pr")_W circle.tiny rho_g^(-1) circle.tiny rho_h^(-1) = 1 / abs(G) sum_(g in G) rho_(h g) circle.tiny op("pr")_W circle.tiny rho_(h g)^(-1) = op("pr")_W^0.
  $
  Rewrite the above equation as
  $
    rho_h circle.tiny op("pr")_W^0 = op("pr")_W^0 circle.tiny rho_h.
  $
  For any $w in W^0$, we have $op("pr")_W^0 circle.tiny rho_h (w) = rho_h circle.tiny op("pr")_W^0 (w) = 0$, which implies $rho_h (w) in ker op("pr")_W^0 = W^0$. Therefore, $W^0$ is $G$-invariant.
]


The following property is called complete reducibility, or semisimplicity.


#proposition[Maschke's theorem][
  $typebadge(
    bb(k), Fld;
    G, FinGrp
  )$

  Suppose $op("char")(bb(k))$ does not divide $|G|$. Then

  + every finite-dimensional representation of a $G$ over $bb(k)$ is a direct sum of irreducible representations.

  + $bb(k)[G]$ is semisimple.

  + $[sans(upright("B"))G, Vect(bb(k))^("fin")]$ is a semi-simple category.
]
#proof[
  Let $G$ be a finite group and $rho:G->GL(V)$ be a finite-dimensional representation. We proceed by induction on $dim V$.

  - If $dim V = 0$, the statement is trivial.

  - Suppose the statement is true for all finite-dimensional representations of $G$ with dimension less than $n$. Given an $n$-dimensional representation $rho:G->GL(V)$, if it is irreducible, then we are done. Otherwise, there exists a proper nontrivial subrepresentation $W$ of $V$. According to @complement-of-invariant-subspace, there exists a complement $W^0$ of $W$ in $V$ such that $V = W plus.circle W^0$ and $W^0$ is also $G$-invariant. By induction hypothesis, $W$ and $W^0$ are direct sums of irreducible representations. Therefore, $V$ is also a direct sum of irreducible representations.
]


#definition[Regular Representation][

]

== Characters of Groups

=== Algebraic Characters of Groups

#definition[Character of a Group][
  $typebadge(G, Grp)$

  Let $G$ be a group. A *character* of $G$ is a group homomorphism $chi: G -> CC^times$. That is, it is a function such that
  $
    chi(g_1 g_2) = chi(g_1) chi(g_2), quad forall g_1, g_2 in G.
  $
]

#definition[Conjugate Character][
  $typebadge(G, Grp)$

  Let $G$ be a group and $chi: G -> CC^times$ be a character of $G$. The *conjugate character* of $chi$ is the character $overline(chi): G -> CC^times$ defined by $overline(chi)(g) = overline(chi(g))$.
]


#definition[Character Group of a Group][
  $typebadge(G, Grp)$

  All characters of $G$ form a $CC^times$-vector space, denoted by $chargrp(G):=op("Hom")_(sans("Grp"))(G,CC^times)$, called the *character group*#index("Ch") of $G$. The group operation is given by pointwise multiplication
  $
    (chi_1 chi_2)(g) = chi_1(g) chi_2(g), quad forall g in G.
  $
  The identity element of $chargrp(G)$ is the *trivial character*
  $
    1_(chargrp(G)): G & --> CC^times \
                    g & mapsto.long 1.
  $
]
#remark[
  If $G$ is a finite abelian group, then we can endow $G$ with discrete topology. Then the character group $chargrp(G)$ is exactly the underlying group of the Pontryagin dual of $G$. In this case, we can just write $chargrp(G) = algdual(G)$.
]
#proposition[Character Group Functor][
  Taking the character group of a group defines a hom functor $frak(X)=op("Hom")_(sans("Grp"))(-, CC^times)$ as follows

  #functor_diagram(
    F: $op("Hom")_(sans("Grp"))(-, CC^times)$,
    C: $sans("Grp")^(op("op"))$,
    D: $sans("Ab")$,
    g: $iota^(op("op"))$,
    X: $G$,
    Y: $H$,
    Fg: $$,
    FX: $chargrp(G)$,
    FY: $chargrp(H)$,
  )

  If we restricted the functor to the category of abelian groups, we get a left exact functor $op("Hom")_(sans("Ab"))(-, CC^times): sans("Ab")^(op("op")) -> sans("Ab")$, which preserves finite biproducts. Therefore, given abelian groups $G$ and $H$, we have natural isomorphism
  $
           chargrp(G) times chargrp(H) & -->^(tilde) chargrp(G times H) \
                        (chi_1, chi_2) & arrow.long.bar lr(((g,h) arrow.long.bar chi_1(g) chi_2(h)), size: #120%) \
    (chi compose i_G, chi compose i_H) & arrow.long.bar.l chi \
  $
  where
  $
    i_G: G & --> G times H \
         g & --> (g, 1_H)
  $
  and
  $
    i_H: H & --> G times H \
         h & --> (1_G, h)
  $
  are the canonical embeddings.
]<character-group-functor>


#proposition[Properties of Characters][
  + If $G$ is a finite group with $abs(G)=n$, then for any character $chi in chargrp(G)$, the image of $chi$ is a subgroup of the group of $n$-th roots of unity, that is,
    $
      im chi subset.eq mu_n= {z in CC : abs(z) = 1, z^n = 1}.
    $
    Hence $chi(g)^n = 1$ for all $g in G$. In this case, $chargrp(G)$ is a finite group and
    $
      |chargrp(G)| <= n^n.
    $
  + The inverse of $chi$ is given by $chi^(-1) = overline(chi)$.
]
#proof[
  + Let $chi in algdual(G)$ be a character of $G$. Then for any $g in G$, we have
    $
      chi(g)^n = chi(g^n) = chi(1) = 1,
    $
    which implies $chi(G) subset.eq mu_n$, where $mu_n$ is the group of $n$-th roots of unity. Therefore, $algdual(G) subset.eq op("Hom")_(sans("Set"))(G,mu_n)$ Since $|mu_n|=n$, we have $|algdual(G)| <= n^n$.
  + For any $g in G$, we have
    $
      chi(g) overline(chi)(g) = chi(g) overline(chi(g)) = |chi(g)|^2 = 1.
    $
]
#definition[Orthogonality of Characters][
  $typebadge(G, FinGrp)$

  Let $G$ be a finite group. We say $G$ has orthogonality of characters if it satisfies the following conditions:

  + For any $chi in chargrp(G)$,
    $
      sum_(g in G) chi(g) & = abs(G)med bold(1)_(chi = 1_chargrp(G))=cases(
                              gap: #0.5em,
                              |G| & " if" chi = 1_chargrp(G),
                              0 & " if" chi eq.not 1_chargrp(G)
                            )
    $
  + For any $g in G$,
    $
      sum_(chi in algdual(G)) chi(g) = abs(chargrp(G))med bold(1)_(g = 1_G)=cases(
        gap: #0.5em,
        abs(algdual(G)) & " if" g = 1_G,
        0 & " if" g eq.not 1_G
      )
    $
]<orthogonality-of-characters>

#proposition[][
  $typebadge(G, FinGrp)$

  Suppose $G$ is a finite group that has orthogonality of characters. Then
  + For any $chi_1, chi_2 in chargrp(G)$, we have
    $
      sum_(g in G) chi_1(g) overline(chi_2)(g) = abs(G) med bold(1)_(chi_1 = chi_2)=cases(
        gap: #0.5em,
        abs(G) & " if" chi_1 = chi_2,
        0 & " if" chi_1 eq.not chi_2
      )
    $
  + For any $g_1, g_2 in G$, we have
    $
      sum_(chi in chargrp(G)) chi(g_1) overline(chi)(g_2) = abs(chargrp(G)) med bold(1)_(g_1 = g_2)=cases(
        gap: #0.5em,
        abs(chargrp(G)) & " if" g_1 = g_2,
        0 & " if" g_1 eq.not g_2
      )
    $
]
#proof[
  + In the first equation, let $chi=chi_1 overline(chi)_2$. Then we have
    $
      sum_(g in G) chi(g) = sum_(g in G) chi_1(g) overline(chi_2)(g) = abs(G) med bold(1)_(chi_1 overline(chi)_2=1_())=cases(
        gap: #0.5em, abs(G) & " if" chi_1 = chi_2, 0 & " if" chi_1 eq.not chi_2
      )
    $
  + In the second equation, let $g=g_1 g_2^(-1)$. Then we have
    $
      sum_(chi in algdual(G)) chi(g) =sum_(chi in chargrp(G)) chi(g_1) overline(chi)(g_2) = abs(chargrp(G)) med bold(1)_(g_1 g_2^(-1)=1_G)=cases(
        gap: #0.5em, abs(chargrp(G)) & " if" g_1 = g_2, 0 & " if" g_1 eq.not g_2
      )
    $
]

#lemma[Orthogonality of Characters of Product Groups][
  $typebadge(G\, H, FinAb)$

  If $G$ and $H$ are finite abelian groups which have orthogonality of characters, then $G times H$ also has orthogonality of characters.
]<orthogonality-of-characters-of-product-groups>
#proof[
  For any $chi in algdual((G times H))$, by @character-group-functor it can written as $chi(g, h)=chi_1(g)chi_2(h)$ for $chi_1=chi compose i_G in algdual(G)$ and $chi_2 =chi compose i_H in algdual(H)$. We can check that
  $
    sum_((g times h) in G times H) chi(g, h) & = sum_((g times h) in G times H) chi_1(g)chi_2(h) \
                                             & =sum_(g in G) chi_1(g) sum_(h in H) chi_2(h) \
                                             & =|G| |H| bold(1)_(chi_1 = 1_(algdual(G))) bold(1)_(chi_2 = 1_(algdual(H))) \
                                             & =|G| |H| bold(1)_(chi = 1_algdual((G times H))).
  $
  For any $g in G$ and $h in H$, we have
  $
    sum_(chi in algdual((G times H))) chi(g, h) & =sum_((chi_1,chi_2) in algdual(G)times algdual(H)) chi_1(g)chi_2(h) \
                                                & =sum_(chi_1 in algdual(G)) chi_1(g) sum_(chi_2 in algdual(H)) chi_2(h) \
                                                & =|algdual(G)| |algdual(H)| bold(1)_(g = 1_G) bold(1)_(h = 1_H) \
                                                & =|algdual(G)| |algdual(H)| bold(1)_((g,h) = 1_(G times H)).
  $
  This shows that $G times H$ has orthogonality of characters.
]

#lemma[
  $typebadge(G, FinAb)$

  Assume that $G$ is a fnite cyclic group of order $n$ and $a in G$ is a generator of $G$. Define a character
  $
    chi: G & --> CC^times \
       a^m & arrow.long.bar e^((2 pi i m ) / n)=zeta_n^(m)
  $
  Then we have
  + For each $k in ZZ$, the $k$-th power of $chi$ is given by
    $
      chi^k: G & --> CC^times \
           a^m & arrow.long.bar e^((2 pi i k m ) / n)=zeta_n^(k m)
    $
  + $algdual(G)$ is a cyclic group of order $n$ generated by the character $chi$ #h(1fr)
    $
      algdual(G) = {chi^k : G -> CC^times mid(|) k=0,1,dots.c,n-1}.
    $
    And we have an isomorphism
    $
        G & -->^(tilde) algdual(G) \
      a^m & arrow.long.bar chi^m.
    $
  + $G$ has #link(<orthogonality-of-characters>)[orthogonality of characters].

]<cyclic-group-characters-lemma>
#proof[
  + This is straightforward.

  + If $theta in algdual(G)$, then $theta(a) in mu_n$ implies $theta(a) = e^((2 pi i k) / n)$ for some $k in {0,1, dots.c, n-1}$. Hence $theta = chi^k$ for some $k in {0,1, dots.c, n-1}$ and we get
    $
      algdual(G) subset.eq {chi^k : G -> CC^times mid(|) k=0,1,dots.c,n-1}.
    $
    Then we can check the inverse inclusion and conclude that
    $
      algdual(G) = {chi^k : G -> CC^times mid(|) k=0,1,dots.c,n-1}.
    $
    Since $chi^k$ are all distinct, we have $|algdual(G)| = n$. Note that both $G$ and $algdual(G)$ are cyclic groups of order $n$ and $a^m |-> chi^m$ sends a generator of $G$ to a generator of $algdual(G)$. We see $a^m |-> chi^m$ is an isomorphism.

  + For any $chi^k in algdual(G)$, we have
    $
      sum_(g in G) chi^k (g)= sum_(m=0)^(n-1)chi^k (a^m) = sum_(m=0)^(n-1) e^((2 pi i k m) / n) = n delta_(k,0) = |G| bold(1)_(chi^k = chi_0).
    $
    For any $a^m in G$ with $m=0,1,dots.c, n-1$, we have
    $
      sum_(chi in algdual(G)) chi(a^m) =sum_(k =0)^(n-1) chi^k (a^m) = sum_(k=0)^(n-1) e^((2 pi i k m) / n) = n delta_(m,0) = |algdual(G)|bold(1)_(a^m = 1_G).
    $

]

#proposition[Orthogonality of Characters of Finite Abelian Group][
  $typebadge(G, FinAb)$

  Let $G$ be a finite abelian group of order $n$ and $a in G$ be a generator of $G$. Then $G tilde.equiv algdual(G)$ and $G$ has orthogonality of characters.
]<orthogonality-of-characters-of-finite-abelian-group>
#proof[
  The fundamental theorem of abelian groups implies that $G$ is isomorphic to a finite direct product of cyclic groups. Then, it follows from @cyclic-group-characters-lemma, @character-group-functor and @orthogonality-of-characters-of-product-groups.
]

#pagebreak()

= Representations of Locally Compact Groups

In this chapter, we study representations of locally compact Hausdorff groups.

== Unitary Representations

#definition[Unitary Representation][
  $typebadge(
    G, LCHGrp;
    H_pi, CHilb
  )$

  A *unitary representation* of a locally compact Hausdorff group $G$ on a complex Hilbert space $H_pi$ is a continuous group homomorphism $pi: G -> U(H_pi)$, where $U(H_pi)$ is the group of unitary operators on $H_pi$ and the topology on $U(H_pi)$ is the topology induced by the strong operator norm.
  The map $pi$ is called a *unitary representation* of $G$.
]

#proposition[][
  $typebadge(
    G, LCHGrp;
    H_pi, CHilb
  )$

  Given a complex Hilbert space $H_pi$, the weak and strong operator topologies coincide on $U(H_pi)$. Let $pi: G -> U(H_pi)$ be group homomorphism. The following statement is equivalent:

  + $pi$ is a continuous  with respect to the strong operator topology.

  + For any $v in H_pi$, the map
    $
      pi_v: G & --> H_pi \
            g & arrow.long.bar pi(g)(v)
    $
    is continuous.

  + For any $u , v in H_pi$, the map
    $
      G & --> CC \
      g & arrow.long.bar angle.l pi(g)(u), v angle.r
    $
    is continuous.
]



#example[][
  $typebadge(
    G, LCHGrp;
    X, Top
  )$

  If a locally compact Hausdorff group $G$ acts on a locally compact Hausdorff space $X$, then $G$ acts on $op("Hom")_(sans("Set"))(X, CC)$, the space of  functions from $X$ to $CC$, by
  $
    G times op("Hom")_(sans("Set"))(X, CC) & --> op("Hom")_(sans("Set"))(X, CC) \
                                    (g, f) & arrow.long.bar (x arrow.long.bar f(g^(-1) x)).
  $
  Moreover, if $X$ admits a $G$-invariant Radon measure $mu$, then the above action gives a unitary representation of $G$ on the Hilbert space $L^2(X, cal(B)(X), mu)$, the space of square integrable functions on $X$ with respect to the measure $mu$. The representation is given by
  $
    pi: G & --> U(L^2(X, cal(B)(X), mu)) \
        g & arrow.long.bar (f arrow.long.bar (x arrow.long.bar f(g^(-1) x))).
  $
]

By considering the action of $G$ on $G$ itself by left multiplication, we get the *left regular representation* of $G$ defined as follows.

#definition[Regular representation][
  $typebadge(G, LCHGrp)$

  Let $G$ be a locally compact Hausdorff group and $mu, rho$ be the left and right Harr measure on $G$, respectively. The *left regular representation* of $G$ is the unitary representation
  $
    pi_L: G & --> U(L^2(G, cal(B)(G), mu)) \
          g & arrow.long.bar (f arrow.long.bar (L_g f: h arrow.long.bar f(g^(-1) h))).
  $
]

#example[Regular representation of $RR$][
  Let $RR$ be the additive group of real numbers. The regular representation of $RR$ on $L^2(RR, cal(B)(RR), mu)$ is given by
  $
    pi_L: RR & --> U(L^2(RR, cal(B)(RR), mu)) \
           x & arrow.long.bar (f arrow.long.bar (L_x f: t arrow.long.bar f(t -x))).
  $
  $pi_L$ has no irreducible subrepresentations.
]
#proof[
  If $pi_L$ has an irreducible subrepresentation $pi^V_L: RR -> U(V)$, then by @irreducible-unitary-representation-of-lca-group-is-one-dimensional we have $dim V =1$. According to @identify-one-dimensional-unitary-representations-of-lca-group-with-characters, there exists a character $chi: RR -> TT$ such that
  $
    pi_L^V (x) (f) = chi(x) f
  $
  for all $x in RR$ and $f in V$. Thus for all $x in RR$, $f in V$, $t in RR$, we have
  $
    [pi_L^V (x) (f)](t)= chi(x) f(t) = f(t - x).
  $
  Take $t=0$ and some $f^* in V-{0}$. Then for all $x in RR$, we have
  $
    f^*(x)=chi(-x) f^*(0)=> abs(f^*(x))=|f^*(0)|,
  $
  which implies $t|->|f^*(t)|$ is a constant function. Since $f^* in L^2(RR, cal(B)(RR), mu)$, we have $f^*=0$, which leads to a contradiction. Therefore, $pi_L$ has no irreducible subrepresentations.

]

#definition[Intertwining Operator][
  $typebadge(
    G, LCHGrp;
    H_1\, H_2, CHilb
  )$

  Let $pi_1: G -> U(H_1)$ and $pi_2: G -> U(H_2)$ be two unitary representations of $G$. An bounded linear operator $T: H_1 -> H_2$ is called an *intertwining operator* if
  $
    T pi_1(g) = pi_2(g) T, quad forall g in G.
  $
  We denote the set of all intertwining operators from $pi_1$ to $pi_2$ by $op("Hom")_(sans("URep"))(pi_1, pi_2)$. And the set of all intertwining operators from $pi$ to itself is denoted by $op("End")_(sans("URep"))(pi):= op("Hom")_(sans("URep"))(pi, pi)$, called
]

#definition[Commutant of a Unitary Representation][
  $typebadge(
    G, LCHGrp;
    H, CHilb
  )$

  Let $pi: G -> U(H)$ be a unitary representation of $G$. The *commutant* of $pi$ is the set of all intertwining operators from $pi$ to itself, which is denoted by $op("End")_(sans("URep"))(pi):= op("Hom")_(sans("URep"))(pi, pi)$.
]

#definition[Unitary equivalence][
  $typebadge(
    G, LCHGrp;
    H_1\, H_2, CHilb
  )$

  Let $pi_1: G -> U(H_1)$ and $pi_2: G -> U(H_2)$ be two unitary representations of $G$. We say $pi_1$ and $pi_2$ are *unitarily equivalent* if there exists a unitary operator $U in op("Hom")_(sans("URep"))(pi_1, pi_2)$ such that
  $
    pi_2(g) = U pi_1(g) U^(-1), quad forall g in G.
  $
]


#definition[Invariant Subspace of a Unitary Representation][
  $typebadge(
    G, LCHGrp;
    H, CHilb
  )$

  Let $pi: G -> U(H)$ be a unitary representation of a locally compact Hausdorff group $G$. An *invariant subspace of $H$ for $pi$* is a closed subspace $V subset.eq H$ such that
  $
    pi(g)(V) subset.eq V, quad forall g in G.
  $
]<invariant-subspace-of-a-unitary-representation>

#definition[Subrepresentation of a Unitary Representation][
  $typebadge(
    G, LCHGrp;
    H\, V, CHilb
  )$

  Let $pi: G -> U(H)$ be a unitary representation of a locally compact Hausdorff group $G$. If $V subset.eq H$ is an #link(<invariant-subspace-of-a-unitary-representation>)[invariant subspace for $pi$], then the map

  $
    pi^V: G & --> U(V) \
          g & arrow.long.bar pi(g)|_V
  $
  is called a *subrepresentation* of $pi$.
]

#definition[Irreducible Representation][
  $typebadge(
    G, LCHGrp;
    H, CHilb
  )$

  A unitary representation $pi: G -> U(H)$ of a locally compact Hausdorff group $G$ is called *irreducible* if the only invariant subspaces of $H$ for $pi$ are $\{0\}$ and $H$ itself. Otherwise, it is called *reducible*.
]


#proposition[Orthogonral Complement of a Invariant Subspace is Invariant
][
  $typebadge(
    G, LCHGrp;
    H\, V, CHilb
  )$

  Let $pi: G -> U(H)$ be a unitary representation of a locally compact Hausdorff group $G$. If $V subset.eq H$ is a invariant subspace for $pi$, then $V^(perp)$ is also a invariant subspace for $pi$. And we have
  $
    pi = pi^V plus.circle pi^(V^(perp)).
  $
]
#proof[
  Let $v in V^(perp)$ and $g in G$. Then for any $w in V$, we have
  $
    pi(g^(-1))(w) in V
  $
  and
  $
    angle.l pi(g)(v), w angle.r =lr(angle.l (pi(g)^(-1) compose pi(g))(v), pi(g)^(-1) (w) angle.r) =angle.l v, pi(g^(-1))(w) angle.r = 0.
  $
  This implies $pi(g)(v) in V^(perp)$. Therefore, $V^(perp)$ is a invariant subspace for $pi$.

  Since $V$ is a closed subspace of $H$, we have direct sum decomposition
  $
    H = V plus.circle V^(perp).
  $
  For any $g in G$ and $v in V$, $v$ can be uniquely written as $v = v_1 + v_2$ with $v_1 in V$ and $v_2 in V^(perp)$. Since
  $
    (pi^V plus.circle pi^(V^(perp)) ) (g)(v) & = (pi^V plus.circle pi^(V^(perp)) ) (g) (v_1 + v_2) \
                                             & = pi^V (g) (v) plus pi^(V^(perp)) (g) (w) \
                                             & = pi^V (g)(v_1) + pi^(V^(perp)) (g)(v_2) \
                                             & = pi (g)(v_1) + pi (g)(v_2) \
                                             & = pi (g)(v_1 + v_2) \
                                             & = pi (g)(v), quad forall g in G, forall v in V,
  $
  we have $pi = pi^V plus.circle pi^(V^(perp))$.
]

#definition[Cyclic Subspace][
  $typebadge(
    G, LCHGrp;
    H_pi, CHilb
  )$

  Let $pi: G -> U(H_pi)$ be a unitary representation of a locally compact Hausdorff group $G$. Suppose $v in H_pi$. The *cyclic subspace generated by $v$* is the closed subspace of $H_pi$ defined by
  $
    M_v := overline(op("span"){pi(g)(v) mid(|) g in G})
  $
]
#remark[
  Clearly, $M_v$ is an invariant subspace for $pi$.
]

#definition[Cyclic Representation][
  $typebadge(
    G, LCHGrp;
    H_pi, CHilb
  )$

  Let $pi: G -> U(H_pi)$ be a unitary representation of a locally compact Hausdorff group $G$.
  - If $H_pi = M_v$, then $v$ is called a *cyclic vector* for $pi$.

  - If $pi$ has a cyclic vector, then $pi$ is called a *cyclic representation* of $G$.
]

#proposition[Every Unitary Representation is a Direct Sum of Cyclic
  Representations][
  $typebadge(
    G, LCHGrp;
    H, CHilb
  )$

  Let $pi: G -> U(H)$ be a unitary representation of a locally compact Hausdorff group $G$. Then there exists a decomposition
  $
    H = plus.big_(alpha in I) M_alpha
  $
  where $M_alpha subset.eq H$ are cyclic subspaces generated by $alpha$. And we have
  $
    pi = plus.big_(alpha in I) pi^(M_alpha).
  $
]

#proposition[Characterization of Invariant Subspaces][
  $typebadge(
    G, LCHGrp;
    H_pi, CHilb
  )$

  Let $pi: G -> U(H_pi)$ be a unitary representation of a locally compact Hausdorff group $G$. Let $M$ be a closed subspace of a Hilbert space $H_pi$. Let $op("pr")_M: H_pi -> M$ be the orthogonal projection onto $M$. Then $M$ is invariant for $pi$ if and only if $op("pr")_M in op("End")_(sans("URep"))(pi)$.
]<characterization-of-invariant-subspaces>
#proof[
  If $M$ is invariant for $pi$, then for any $g in G$ and $v in M$, we have
  $
    pi(g)(op("pr")_M (v)) =pi(g)(v)= op("pr")_M (pi(g) (v)).
  $
  And for any $g in G$ and $w in M^perp$, we have
  $
    pi(g)(op("pr")_M (w)) = 0=op("pr")_M (pi(g) (w)).
  $
  This implies $op("pr")_M in op("End")_(sans("URep"))(pi)$.

  Conversely, if $op("pr")_M in op("End")_(sans("URep"))(pi)$, then for any $g in G$ and $v in M$, we have
  $
    pi(g)(v)=pi(g)(op("pr")_M (v)) = op("pr")_M (pi(g) (v)) in M.
  $
  which implies $M$ is invariant for $pi$.
]

#theorem[Schur's Lemma for Unitary Representations][
  $typebadge(
    G, LCHGrp;
    H_pi\,H_1\, H_2, CHilb
  )$

  + Let $pi: G -> U(H_pi)$ be a unitary representation of $G$. Then
    $
      pi "is irreducible" <==> op("End")_(sans("URep"))(pi) = {lambda id_H_pi mid(|) lambda in CC}.
    $

  + Let $pi_1: G -> U(H_1)$ and $pi_2: G -> U(H_2)$ be two irreducible unitary representations of  $G$. Then
    $
      dim op("Hom")_(sans("URep"))(pi_1, pi_2) = cases(
        gap: #0.5em,
        1\, & quad " if" pi_1 "is unitarily equivalent to" pi_2,
        0\, & quad " otherwise".
      )
    $
]<Schur-lemma-for-unitary-representations>
#proof[
  + If $pi$ is reducible, then there exists a nontrivial invariant subspace $V subset.eq H_pi$. Let $op("pr")_V: H_pi -> V$ be the orthogonal projection onto $V$. Then by @characterization-of-invariant-subspaces, we have $op("pr")_V in op("End")_(sans("URep"))(pi)$ and
    $
      op("End")_(sans("URep"))(pi) eq.not {lambda id_H_pi mid(|) lambda in CC}.
    $
    Conversely, suppose $T in op("End")_(sans("URep"))(pi)$ and $T eq.not lambda id_H_pi$ for any $lambda in CC$.
    Let
    $
      A = 1/2(T + T^*),quad B = 1/(2i)(T - T^*).
    $
    Note $T= A + i B$. We see that $A$ or $B$ is not a multiple of the identity operator, otherwise $T$ is a multiple of the identity operator. Assume $A eq.not lambda id_H_pi$ for any $lambda in CC$.

]

#corollary[Irreducible Unitary Representation of LCA Group is One-dimensional][
  $typebadge(
    G, LCA;
    H_pi, CHilb
  )$

  Let $pi: G -> U(H_pi)$ be a unitary representation of a locally compact Hausdorff abelian group $G$. Then
  $
    pi "is irreducible" <==> dim H_pi = 1.
  $
]<irreducible-unitary-representation-of-lca-group-is-one-dimensional>
#proof[
  Since $G$ is abelian, for any $g in G$, we have
  $
    pi(g)pi(h)=pi(g h)=pi (h g)=pi(h)pi(g), quad forall h in G,
  $
  which implies $pi(g) in op("End")_(sans("URep"))(pi)$. Suppose $pi$ is irreducible. By @Schur-lemma-for-unitary-representations, for each $g in G$, there exists a $lambda_g in CC$ such that
  $
    pi(g)= lambda_g id_H_pi.
  $
  which implies every one-dimensional subspace of $H_pi$ is invariant for $pi$. Assume $V$ is a one-dimensional subspace of $H_pi$.
  The irreducibility of $pi$ implies that the only invariant subspaces of $H_pi$ are ${0}$ and $H_pi$ itself, which forces $V= H_pi$. Therefore, $dim H_pi = 1$.
]


== Group Algebra of a Representation

#definition[$*$-Representation of Banach $*$-Algebra][
  $typebadge(H, CHilb)$

  Let $A$ be a Banach $*$-algebra. A *$*$-representation* of $A$ on a complex Hilbert space $H$ is a $*$-homomorphism $phi.alt: A -> op("End")_CHilb (H)$.
]<star-representation-of-banach-star-algebra>
#remark[
  The norm-closure of $phi.alt(A)$ is a $upright(C)^*$-subalgebra of $op("End")_CHilb (H)$, which is a Banach $*$-algebra.
]

#definition[Nondegenerate $*$-Representation of Banach $*$-Algebra][
  $typebadge(H, CHilb)$

  A $*$-representation $phi.alt: A -> op("End")_CHilb (H)$ of a Banach $*$-algebra $A$ is called *nondegenerate* if one of the following equivalent conditions holds:

  + The norm-closure of $phi.alt(A)$ is nondegenerate.

  + There exists no nonzero $v in H$ such that for all $a in A$,
    $
      phi.alt(a)(v) = 0.
    $

]

#definition[$*$-representation of $L^1(G)$][
  $typebadge(
    G, LCA;
    H_pi, CHilb
  )$

  Let $G$ be a locally compact Hausdorff abelian group and $pi: G -> U(H_pi)$ be a unitary representation of $G$. For each $u in H_pi$, define
  $
    pi_u: G & --> H_pi \
          g & arrow.long.bar pi(g)(u).
  $
  Then $pi_u$ is a bounded continuous map from $G$ to $H_pi$. For any $f in L^1(G, cal(B)(G), mu)$, the weak integral $integral_G f pi_u dif mu in H_pi$ exists, which satisfies
  $
    integral_G f(g) angle.l pi(g)(u),v angle.r dif mu(g) = lr(angle.l integral_G f pi_u dif mu, v angle.r),quad forall v in H_pi.
  $

  So we can define a representation of $L^1(G, cal(B)(G), mu)$ on $H_pi$ by
  $
    tilde(pi): L^1(G, cal(B)(G), mu) & --> op("End")_CHilb (H_pi) \
    f & arrow.long.bar (u arrow.long.bar tilde(pi)(f)(u):=integral_G f pi_u dif mu=integral_G f(g)pi(g)(u) dif mu (g)).
  $
  $tilde(pi)$ is a nondegenerate $*$-representation of $L^1(G, cal(B)(G), mu)$.
]
#remark[
  It is easy to check that $tilde(pi)$ is a linear map and
  $
    norm(tilde(pi)(f)(u))_H_pi <= integral_G |f(g)| norm(pi(g)(u))_H_pi dif mu(g) <= norm(f)_1 norm(u)_H_pi, quad forall f in L^1(G, cal(B)(G), mu), forall u in H_pi.
  $
  So for any $f in L^1(G, cal(B)(G), mu)$, we have $tilde(pi)(f) in op("End")_CHilb (H_pi)$, which means that $tilde(pi)$ is well-defined. And we have
  $
    norm(tilde(pi)(f))_(op("op")) <= norm(f)_1, quad forall f in L^1(G, cal(B)(G), mu).
  $

]



== Quasi‑character of Restricted Product
In this section, we assume that $I$ is an index set and $F subset.eq I$ is a finite subset of $I$. Suppose $G_i$ is a locally compact Hausdorff abelian group for each $i in I$, and
$H_v subset.eq G_v$ is an open compact subgroup for each $v in I - F$.
Let $ G := product_(v in I)^' G_v $ be the restricted product of the
groups $G_v$ with respect to the open compact subgroups $H_v$.
Let
$
  S_g := F union {v in I - F mid(|) g_v in.not H_v}
$
Let
$
  i_v: G_v & --> G \
       g_v & arrow.long.bar (1, dots.c, 1, g_v, 1, dots.c, 1),
$
be the canonical embedding of $G_v$ into $G$.

#example[Canonical Embedding of $G_v$][
  Define
  $
    i_v: G_v & --> G \
         g_v & arrow.long.bar (1, dots.c, 1, g_v, 1, dots.c, 1),
  $
  We say $i_v in op("Hom")_(sans("TopGrp"))(G_v, G)$ is the *canonical embedding* of $G_v$ into $G$. It is a continuous injective group homomorphism.
]

#example[Local Quasi-character][
  Let $omega in op("Hom")_(sans("TopGrp"))(G, CC^times)$ be a quasi-character of $G$. Then
  $
    omega_v: G_v & --> CC^times \
             g_v & arrow.long.bar omega(i_v (g_v))
  $
  is a quasi-character of $G_v$ for each $v in I$.
]

#lemma[No Small Subgroup][
  A topological group $G$ is said to have no small subgroup if there exists a neighborhood $U$ of the identity $1_G$ that contains no nontrivial subgroup of $G$. Any Lie group has no small subgroups.
]<no-small-subgroup>

#proposition[][
  Let $omega in op("Hom")_(sans("TopGrp"))(G, CC^times)$ be a quasi-character of $G$. Then

  + $omega_v|_(H_v) =1$ for all but finitely many $v in I - F$.

  + For any $g in G$, we have
    $
      omega(g) = product_(v in I) omega_v (g_v).
    $
    Here this product is understood as a finite product, that is, it is taken over ${v in I mid(|) omega_v (g_v) eq.not 1}$.
]
#proof[
  According to @no-small-subgroup, there exists a neighborhood $U$ of $1$ such that ${1}$ is the only subgroup of $CC^times$ contained in $U$. Let
  $
    N=product_(v in I)N_v
  $
  be a neighborhood of $1_G$ in $G$ such that $omega(N)subset.eq U$, with $N_v=H_v$ for all $v in I - S$ where $S$ is a finite subset of $I$. Let
  $
    H:= product_(v in S){1_(G_v)} times product_(v in I - S)H_v .
  $
  Then $H subset.eq N$ and $H$ is a subgroup of $G$. Since $omega(H)$ is a subgroup of $CC^times$ and $omega(H)subset.eq U$, we have $omega(H)={1}$, which implies
  $
    omega|_(H_v) =1,quad forall v in I - S.
  $
  Now given $g in G$, we can write $g=(g_v)_(v in I)$ as
  $
    g = (product_(v in S union S_g) i_v (g_v) )g',quad g' in H
  $
  Then we have
  $
    omega(g) & = omega(g')product_(v in S union S_g) omega (i_v (g_v)) \
             & = product_(v in S union S_g) omega_v (g_v) .
  $
]

#proposition[][
  Let $omega_v in op("Hom")_(sans("TopGrp"))(G_v, CC^times)$ be a quasi-character of $G_v$ for each $v in I$. Assume $omega_v|_(H_v) =1$ for all $v in I - S$ with $S$ is a finite subset of $I$. Define
  $
    omega: G & --> CC^times \
           g & arrow.long.bar product_(v in I) omega_v (g_v).
  $
  Then $omega in op("Hom")_(sans("TopGrp"))(G, CC^times)$ is a quasi-character of $G$.
]
#proof[
  For any $g in G$, we have
  $
    v in I - (S union S_g) & ==> v in (I - S) inter (I- S_g) \
                           & ==> omega_v|_(H_v) =1 "and" g_v in H_v \
                           & ==> omega_v (g_v) =1 \
                           & ==> v in.not {v in I mid(|) omega_v (g_v) eq.not 1},
  $
  which implies
  $
    v in {v in I mid(|) omega_v (g_v) eq.not 1} ==> v in S union S_g.
  $
  So we see
  $
    {v in I mid(|) omega_v (g_v) eq.not 1} subset.eq S union S_g.
  $
  Since $S union S_g$ is a finite set, ${v in I mid(|) omega_v (g_v) eq.not 1}$ is also a finite set. Therefore,
  $
    omega(g) = product_(v in I) omega_v (g_v) = product_(v in S union S_g) omega_v (g_v)
  $
  is a well-defined finite product.

  It is straightforward to check that $omega$ is a group homomorphism:
  For any $g, h in G$, we have
  $
    omega(g h) & = product_(v in S union S_g) omega_v (g_v h_v) \
               & = product_(v in S union S_g) omega_v (g_v) omega_v (h_v) \
               & = (product_(v in S union S_g) omega_v (g_v))( product_(v in S union S_h) omega_v (h_v)) \
               & = omega(g) omega(h).
  $

  What remains is to check that $omega$ is continuous. Let $U$ be a neighborhood of $1$ in $CC^times$. Let $n:=|S|$. By the property of topological groups, there exists a neighborhood $V$ of $1$ in $CC^times$ such that
  $
    V^((n)):={g_1g_2 thin dots.c thin g_n mid(|) g_i in V "for" i=1,2,dots.c,n} subset.eq U.
  $
  For each $v in S$, there exists a neighborhood $N_v$ of $1_(G_v)$ such that
  $
    omega_v (N_v)subset.eq V.
  $
  It follows that
  $
    N:= product_(v in S)N_v times product_(v in I - S)H_v
  $
  is a neighborhood of $1_G$ in $G$ such that
  $
    omega(N) =omega(product_(v in S)N_v times product_(v in I - S)H_v) = {product_(v in S) omega_v (g_v) mid(|) g_v in N_v "for" v in S} subset.eq V^((n)) subset.eq U,
  $
  which shows that $omega$ is continuous.
]

#pagebreak()

= Duality for Locally Compact Abelian Groups


== Pontryagin Dual

#definition[Circle Group][
  The *circle group* is defined as
  $
    TT = {z in CC : abs(z) = 1} = U(1)
  $
  equipped with the multiplication of complex numbers and the topology induced from the standard topology of $CC$.
]
#lemma[][
  $typebadge(H, CHilb)$

  If $H$ is a one-dimensional complex Hilbert space,  then
  $
    U(H) = {lambda id_H mid(|) lambda in TT} tilde.equiv TT.
  $
  Suppose $U(H)$ is equipped with the strong operator topology and $e in H$ is a unit vector in $H$. Then the map
  $
                     phi: TT & -->^(tilde) U(H) \
                      lambda & arrow.long.bar lambda id_H \
    angle.l U (e), e angle.r & arrow.long.bar.l U
  $
  is a topological group isomorphism.
]<unitary-group-of-one-dimensional-hilbert-space>
#proof[
  Since $dim H =1$, there exists a unit vector $v in H$ such that $H = {c v mid(|) c in CC}$. Fix a unitary operator $U in U(H)$. There exists a unique $lambda in CC$ such that $U(v)=lambda v$. Note
  $
    abs(lambda) =abs(lambda) norm(v)=norm(lambda v)=norm(U(v))= norm(v) =1.
  $
  For any $x =c v in H$, we have
  $
    U(x)=U(c v) = c U(v) = c lambda v = lambda x.
  $
  Hence $U= lambda id_H$.

  Conversely, for any $lambda in T$, we can check that
  $
    (lambda id_H)^* (lambda id_H)=(lambda id_H) (lambda id_H)^*=overline(lambda) lambda id_H id_H = id_H,
  $
  which implies $lambda id_H in U(H)$.

  It is straightforward to check that the map $phi$ is a group homomorphism. Since $T$ is compact and $U(H)$ is Hausdorff, if we can show that $phi$ is continuous, then it is a homeomorphism. The topology on $U(H)$ is the initial topology with respect to the family of maps
  $
    op("ev")_v : U(H) & --> H \
                    U & arrow.long.bar U(v)
  $
  for all $v in H$. For any $v in H$, we have
  $
    op("ev")_v compose phi (lambda) = op("ev")_v (lambda id_H) = lambda v, quad forall lambda in TT.
  $
  Note that in a normed space the map, the scalar multiplication map $(lambda,v) & arrow.long.bar lambda v$ is continuous in each variable separately. We can conclude that $op("ev")_v compose phi$ is continuous for each $v in H$. By the characteristic property of the initial topology, we see that $phi$ is continuous.
]



#definition[Pontryagin Dual of a Locally Compact Abelian Group][
  $typebadge(G, LCA)$

  Let $G$ be a locally compact Hausdorff abelian group. The *Pontryagin dual* of $G$ is a topological group $algdual(G)$ defined as follows
  + Underlying set:
    $
      algdual(G) = op("Hom")_(sans("TopAb"))(G, TT),
    $
    where $TT$ is the circle group.

  + Group Multiplication: $algdual(G)subset.eq op("Hom")_(sans("Ab"))(G, TT)$ is an abelian group with the pointwise multiplication of functions: given $chi_1, chi_2 in algdual(G)$, their multiplication $chi_1 chi_2$ is defined By
    $
      chi_1 chi_2: G times G & --> TT \
                  (g_1, g_2) & arrow.long.bar chi_1(g_1) chi_2(g_2)
    $

  + Identity element: The identity element in $algdual(G)$ is the constant function 1
    $
      1_algdual(G): G & --> TT \
                    g & arrow.long.bar 1
    $

  + Topology: $algdual(G)$ is equipped with the compact-open topology.
]
#corollary[][
  $typebadge(
    G, LCA;
    H, CHilb
  )$

  Let $G$ be a locally compact Hausdorff abelian group and $H$ be a one-dimensional complex Hilbert space. Let $e in H$ be a unit vector in $H$. There is a bijection
  $
          algdual(G)=op("Hom")_(sans("TopAb"))(G, TT) & -->^(tilde) op("Hom")_(sans("TopGrp"))(G, U(H)) \
                                                  chi & arrow.long.bar (pi: g arrow.long.bar chi(g) id_H) \
    (chi: g mapsto.long angle.l pi(g) (e), e angle.r) & arrow.long.bar.l pi
  $
  between $op("Hom")_(sans("TopAb"))(G, TT)$ and one-dimensional unitary representations of $G$.
]<identify-one-dimensional-unitary-representations-of-lca-group-with-characters>
#proof[
  According to @unitary-group-of-one-dimensional-hilbert-space, we have the topological group isomorphism $U(H) tilde.equiv TT$. This gives the desired bijection.

]

#proposition[][
  $typebadge(G, LCA)$

  Let $G$ be a locally compact Hausdorff abelian group with a Haar measure $mu$. Then

  + Given any $chi in algdual(G)$, the map
    $
      xi_chi: L^1(G) & --> CC \
                   f & mapsto.long integral_G lr(angle.l x, chi angle.r) f(x) dif mu(x) = integral_G f(x) chi(x) dif mu(x)
    $
    is a multiplicative functional on $L^1(G)$, i.e. a nonzero Banach algebra homomorphism.

  + The map
    $
      xi_(bullet): algdual(G) & --> sigma(L^1(G)) \
                          chi & mapsto.long xi_chi
    $
    is a homeomorphism.
]
#proof[
  + Since for any $f in L^1(G)$,
    $
      norm(xi_chi (f)) = abs(integral_G lr(angle.l x, chi angle.r) f(x) dif mu(x)) <= integral_G abs(f(x))abs(chi(x)) dif mu(x) = norm(f)_1,
    $
    we see that $xi_chi$ is a well-defined continuous linear functional on $L^1(G)$.

    - _Multiplicativity_. Using Fubini-Tonelli theorem, we have for any $f, g in L^1(G)$,
    $
      xi_chi (f*g) & = integral_G (f*g)(x) thin chi(x) dif mu(x) \
                   & = integral_G integral_G f(y) g(y^(-1) x) thin chi(x) dif mu(y) dif mu(x) \
                   & = integral_G f(y) (integral_G g(w) thin chi(y w) dif mu(w)) dif mu(y) quad (x = y w) \
                   & = integral_G f(y) chi(y) dif mu(y) integral_G g(w) chi(w) dif mu(w) \
                   & = xi_chi (f) thin xi_chi (g).
    $

    - _$*$-preservation_. For any $f in L^1(G)$, we have
    $
      xi_chi (f^*) & = integral_G f^*(x) chi(x) dif mu(x) \
                   & = integral_G overline(f(x^(-1))) chi(x) dif mu(x) \
                   & = integral_G overline(f(y)) chi(y^(-1)) dif mu(y) quad (x = y^(-1)) \
                   & = overline(integral_G f(y) chi(y) dif mu(y)) \
                   & = xi_chi (f)^*.
    $

    Therefore, $xi_chi$ is a multiplicative functional on $L^1(G)$.

  +
    - _Injectivity_. If there exist $chi, psi in algdual(G)$ such that $xi_chi = xi_psi$, then for any $f in L^1(G)$, we have
    $
      integral_G (chi - psi)f dif mu= xi_chi (f) - xi_psi (f) = 0.
    $
    which implies $chi = psi$ a.e. Since both $chi$ and $psi$ are continuous, we have $chi = psi$.

    - _Surjectivity_. Let $psi in sigma(L^1(G))$. Since $L^1(G)' tilde.equiv L^oo (G)$, there exists $h in L^oo (G)$ such that
      $
        psi(f) = integral_G f h dif mu, quad forall f in L^1(G).
      $
      Since $psi$ is multiplicative, we have for any $f, g in L^1(G)$,
      $
          & integral_G psi(L_x f) g(x) dif mu(x) \
        = & integral_G integral_G f(x^(-1)y) h(y) g(x) dif mu(y) dif mu(x) \
        = & integral_G (f * g)(y) h(y) dif mu(y) \
        = & psi(f * g) \
        = & psi(f) integral_G g(x) h(x) dif mu(x) \
        = & integral_G psi(f) h(x)g(x) dif mu(x),
      $
      which implies for any $f in L^1(G)$ and $mu$-almost every $x in G$,
      $
        psi(L_x f) = psi(f) h(x).
      $
      Since $psi eq.not 0$, we can choose $f_0 in L^1(G)$ with $psi(f_0) eq.not 0$, and define
      $
        chi(x):=psi(L_x f_0)/psi(f_0), quad forall x in G.
      $
      By the continuity of
      $
        G & --> L^1(G) \
        x & arrow.long.bar L_x f_0
      $
      and continuity of $psi$, we see that $chi$ is continuous. Note
      $
        chi(x y) & = psi(L_(x y) f_0)/psi(f_0) \
                 & = psi(L_x (L_y f_0))/psi(f_0) \
                 & = (psi(L_y f_0)h(x))/psi(f_0) \
                 & = (psi(f_0)h(y)h(x))/psi(f_0) \
                 & = (psi(f_0)h(x))/psi(f_0) (psi(f_0)h(y))/psi(f_0) \
                 & = psi(L_(x ) f_0)/psi(f_0) psi(L_(y) f_0)/psi(f_0) \
                 & = chi(x) chi(y).
      $
      We see $chi : G -> CC^times$ is a continuous homomorphism. Since
      $
        abs(chi(x)) = abs(psi(L_x f_0))/abs(psi(f_0)) <= (norm(psi)norm(L_x f_0)_1 )/abs(psi(f_0)) = (norm(psi)norm(f_0)_1 )/abs(psi(f_0)),
      $
      $chi$ is bounded, which forces $abs(chi(x))=1$ for all $x in G$. In fact, if $abs(chi(x_0)) > 1$ for some $x_0 in G$, then as $n -> +oo$,
      $
        abs(chi(x_0)^n)= abs(chi(x_0))^n --> oo,
      $
      which contradicts the boundedness of $chi$. Similarly, we can rule out the case $abs(chi(x_0)) < 1$ since $abs(chi(x_0^(-1))) > 1$ gives the same contradiction. Thus we have $chi in algdual(G)$. Since $chi = h$ a.e., we have
      $
        xi_chi (f) = integral_G f(x) chi(x) dif mu (x) = integral_G f(x) h(x) dif mu (x) = psi(f), quad forall f in L^1(G).
      $
      So $xi_chi = psi$. Surjectivity follows.

]

#example[$*$-representation of $L^1(G)$][
  $typebadge(G, LCA)$

  Let $G$ be a locally compact Hausdorff abelian group and $pi: G -> U(CC)$ be a unitary representation of $G$. By @identify-one-dimensional-unitary-representations-of-lca-group-with-characters, $pi$ corresponds to some $chi in algdual(G)$.
  For each $u in CC$, define
  $
    pi_u: G & --> CC \
          x & arrow.long.bar pi(x)(u).
  $
  Then $pi_u$ is a bounded continuous map from $G$ to $CC$. For any $f in L^1(G, cal(B)(G), mu)$, the weak integral $integral_G f pi_u dif mu in CC$ exists, which satisfies
  $
    integral_G f(x) angle.l pi(x)(u),v angle.r dif mu(x) = lr(angle.l integral_G f pi_u dif mu, v angle.r),quad forall v in CC.
  $

  So we can define a representation of $L^1(G, cal(B)(G), mu)$ on $CC$ by
  $
    tilde(pi): L^1(G, cal(B)(G), mu) & --> op("End")_CHilb (CC) \
    f & arrow.long.bar (u arrow.long.bar tilde(pi)(f)(u):=integral_G f pi_u dif mu=integral_G f(x)pi(x)(u) dif mu (x)).
  $
  $tilde(pi)$ is a nondegenerate #link(<star-representation-of-banach-star-algebra>)[$*$-representation] of $L^1(G, cal(B)(G), mu)$. Through the bijection
  $
                         CC & -->^(tilde)op("End")_CHilb (CC) \
                          z & arrow.long.bar z id_CC \
    angle.l T(1), 1 angle.r & arrow.long.bar.l T
  $
  $tilde(pi)$ can be identified with
  $
    xi_chi:L^1(G, cal(B)(G), mu) & --> CC \
    f & arrow.long.bar integral_G f(x) chi(x) dif mu (x)=integral_G angle.l x, chi angle.r f(x) dif mu(x).
  $
]
#proof[
  - _Nondegeneracy_. Suppose $u eq.not 0$ and $tilde(pi) ( f ) u = 0$ for every $f in L^1 (G)$. Then
    $
      integral f (x) chi (x)dif mu (x) = 0
    $
    for all $f$. Choose any nonzero $g in L^1 \( G \)$ with $g gt.eq 0$ and set $f = macron(chi) g in L^1 \( G \)$. Then
    $
      integral_G f (x) chi (x) dif mu (x) = integral_G g (x) dif mu (x) > 0
    $
    a contradiction. Hence there is no nonzero $u$ annihilated by all $tilde(pi) (f)$, so $tilde(pi)$ is nondegenerate.
]
#proposition[Properties of Pontryagin Dual][
  $typebadge(G, LCA)$

  Suppose $G$ is a locally compact Hausdorff abelian group. Then

  + $G$ is discrete $==>$ $algdual(G)$ is a compact.

  + $G$ is compact $==>$ $algdual(G)$ is discrete.

  + $G$ is discrete and torsion-free $==>$ $algdual(G)$ is a compact and connected.

  + $G$ is compact and connected $==>$ $algdual(G)$ is discrete and torsion-free.

  + $G$ is finite $==>$ $algdual(G)$ is finite.

]

#example[Examples of Pontryagin Dual][
  + $algdual(T) tilde.equiv ZZ$.
  + $algdual(ZZ) tilde.equiv T$.
  + $algdual(RR) tilde.equiv RR$.
  + $algdual(((ZZ\/n ZZ)^times)) tilde.equiv (ZZ\/n ZZ)^times$.
]

#example[$C_c (G)$ is Dense in $L^p (G)$][
  $typebadge(G, LCA)$

  Let $G$ be a locally compact abelian group. We use $C_c (G)$ to denote the space of continuous complex-valued functions on $G$ with compact support.
]

#definition[Functions of Positive Type][
  $typebadge(G, LCA)$

  A Haar measurable function function $phi: G -> CC$ is called a *function of positive type* if for any $f in C_c (G)$, we have
  $
    integral_G integral_G phi(g^(-1) h) f(g) dif mu(g) overline(f(h)) dif mu(h) >= 0.
  $
]


== Fourier Transform


#definition[Fourier Transform on $L^1(G)$][
  $typebadge(G, LCA)$

  Let $G$ be a locally compact abelian group and $mu$ be a Haar measure on $G$. The *Fourier transform* of a function $f in L^1(G)$ is defined as
  $
    hat(f): algdual(G) & --> CC \
                   chi & mapsto.long integral_G f(g) overline(chi(g)) dif mu .
  $
  The Fourier transform is a continuous linear map from $L^1(G)$ to $L^oo (algdual(G))$ defined by
  $
    cal(F): L^1(G) & --> L^oo (algdual(G)) \
                 f & mapsto.long hat(f).
  $
]
#remark[
  Note $abs(chi(g))=1$ for all $g in G$ and $chi in algdual(G)$. For any $f in L^1(G)$ and $chi in algdual(G)$, we have
  $
    abs(hat(f)(chi)) = abs(integral_G f(g) overline(chi(g)) dif mu(g)) <= integral_G abs(f(g)) dif mu(g) = norm(f)_(L^1(G)).
  $
  Thus for any $f in L^1(G)$, we have
  $
    norm(hat(f))_(L^oo (algdual(G)))= sup_(chi in algdual(G)) abs(hat(f)(chi)) <= norm(f)_(L^1(G)) <infinity,
  $
  which implies $cal(F)f=hat(f) in L^oo (algdual(G))$.
]

#pagebreak()

= Number Theory <number-theory>

== Questions
#example[Fermat's Theorem on Sums of Two Squares][
  + Which primes $p$ are sums of two squares? In other words, for which primes $p$ does the equation
    $
      p = x^2 + y^2
    $
    have integer solutions $(x,y) in ZZ^2$?

    *Answer*: If $p$ is a prime number and $p equiv 1 pmod(4)$, then there integers $x$ and $y$ such that
    $
      p = x^2 + y^2= (x+y i)(x-y i).
    $
    For example,
    $
       5 & =2^2+1^2 =(2+i)(2-i), \
      13 & =3^2+2^2=(3+2i)(3-2i), \
      17 & =4^2+1^2=(4+i)(4-i).
    $
    If $p$ is a prime number and $p equiv 3 pmod(4)$, then there are no rational numbers $a$ and $b$ such that $p = x^2 + y^2$.

  + Moreover, we have the following tables for more cases:
  #align(center)[
    #show table.cell.where(y: 0): strong
    #table(
      columns: 3,
      stroke: none,
      row-gutter: 0.1em,
      inset: 8pt,
      table.hline(),
      table.header([Equation], [Has integer solutions], [Number ring]),
      table.hline(stroke: 0.5pt),
      [$p=x^2+y^2$], [$p equiv 1 pmod(4)$], [$ZZ[sqrt(-1)thin]$],
      [$p=x^2+2y^2$], [$p equiv 1 "or" 3 pmod(8)$], [$ZZ[sqrt(-2)thin]$],
      [$p=x^2+3y^2$], [$p equiv 1 pmod(3)$], [$ZZ[sqrt(-3)thin]$],
      [$p=x^2-2y^2$], [$p equiv 1 "or" 7 pmod(8)$], [$ZZ[sqrt(2)thin]$],
      table.hline(),
    )
  ]
]
#remark[
  Note
  $
    p = x^2 + y^2 <==> p = (x+y i)(x-y i) ==> "prime ideal" p ZZ "splits in" ZZ[i].
  $
]

#example[Pell's Equation][
  If $n$ is a positive integer that is not a perfect square, then the equation
  $
    x^2 - n y^2 =(x+y sqrt(n))(x-y sqrt(n))= 1
  $
  has infinitely many integer solutions $(x,y) in ZZ^2$. In other words, the unit group $(ZZ[sqrt(n)thin])^times$ is an infinite group.
]

#example[Sum of Four Squares][
  If $n$ is a positive integer, then the following equation
  $
    x^2 + y^2 + z^2 + w^2 = n
  $
  has integer solutions $(x,y,z,w) in ZZ^4$.
]

A triangle number is an integer of the form $T_n =1/2 n(n+1)$ for some $n in ZZ_(>0)$.

#example[][
  A triangular number different from 1 is not a cubic number. Furthermore, the equation
  $
    1 / 2 n(n+1) = m^3.
  $
  has a unique positive integer solution $(n,m)=(1,1)$.
]

#example[][
  The equation
  $
    y^2 = x^3-2
  $
  has exactly 2 integer solution $(x,y)=(3,plus.minus 5)$.
]

#example[][
  The equation
  $
    y^2 = x^3-4
  $
  has exactly 4 integer solutions $(x,y)=(2,plus.minus 2)$ and $(x,y)=(5,plus.minus 11)$.
]

#definition[Height of a Rational Number][
  Suppose $q=a/b$ is a rational number and $a,b in ZZ$ are coprime. The *height* of a rational number $a / b$ is defined as
  $
    H(a / b) = max { |a|, |b| }.
  $
]

#example[][
  Suppose $d in QQ$. Consider the equation
  $
    y^2 = x^3-d^2 x
  $
  + If $d=1$ or $d=2$, then the equation has exactly 3 rational solutions: $(0,0)$ and $(plus.minus d,0)$.

  + If this equation has a rational solution $(x,y)$ other than $(0,0)$ and $(plus.minus d,0)$, then it has infinitely many rational solutions.
]

#example[Fermat's Last Theorem][
  Suppose $n >= 3$ is an integer. The equation
  $
    x^n + y^n = z^n
  $
  has no positive integer solutions $(x,y,z)$ other than $(0,0,0)$.
]

== Rational points on Quadratic Curves
Give an algebraic curve $C:f(x)=0$ embedded in $bold("A")_(bb(k))^n$. We define the set of $bb(k)$-rational points on $C$ as
$
  C(bb(k)):={ x in bold("A")_(bb(k))^n mid(|) f(x)=0 }.
$
$QQ$-rational points are also called rational points for simplicity.


#proposition[][
  + Consider circle as an affine curve defined by the equation
    $
      C: x^2 + y^2 = 1.
    $
    Then we have the following bijection
    $
                         f:C(QQ)-{(-1,0)} & -->^(tilde) QQ \
                                    (x,y) & mapsto.long y / (x+1), \
      ((1-t^2) / (1+t^2), (2t) / (1+t^2)) & arrow.bar.long.l t.
    $
    which maps the rational point $(x,y)$ on the circle to the slope of the line passing through the point $(x,y)$ and the point $(-1,0)$ on the circle.
  + Consider circle as a projective curve defined by the equation
    $
      C': X^2 + Y^2 = Z^2.
    $
    Then we have the following bijection
    $
            overline(f):C'(QQ) & -->^(tilde) bold("P")_QQ^1=QQ union.sq {oo} \
                       [X:Y:Z] & mapsto.long cases(
                                   [Y: X+Z] & quad " if" X+Z eq.not 0,
                                   [1,0] & quad " if" X+Z = 0
                                 ) \
      [S^2-R^2: 2R S: R^2+S^2] & arrow.bar.long.l [R:S].
    $
]
For a general irreducible projective quadratic curve $C$, if it has a rational point $x in C(QQ)$, then we can construct a bijection
$
  C(QQ) & -->^(tilde) bold("P")_QQ^1
$
in a similar way.

== Reciprocity Laws

#definition[Quadratic Residue][
  Let $p$ be a prime number and $a in ZZ$ be an integer. The integer $a$ is called a *quadratic residue* modulo $p$ if the equation
  $
    x^2 equiv a pmod(p)
  $
  has a solution $x in ZZ$. Otherwise, $a$ is called a *quadratic non-residue* modulo $p$.
]

#proposition[Equivalent Characterization of Quadratic Residue][
  Let $p$ be a prime number and $a in ZZ$ be an integer. Then the following statements are equivalent:

  + $a$ is a quadratic residue modulo $p$.

  + The polynomial $x^2 - a in FF_p [x]$ splits over $FF_p$.

  + The field $FF_p [x] \/ (x^2 - a)$ is isomorphic to $FF_p$.

  Also the following statements are equivalent:

  + $a$ is a quadratic non-residue modulo $p$.

  + The polynomial $x^2 - a in FF_p [x]$ is irreducible over $FF_p$.

  + The field $FF_p [x] \/ (x^2 - a)$ is isomorphic to $FF_(p^2)$.
]


#definition[Legendre Symbol][
  Let $p$ be an odd prime number and $a in ZZ$ be an integer. The *Legendre symbol* is defined as
  $
    (a / p) & = \# {x in FF_p | x^2 = overline(a) } - 1 \
            & = cases(
                0 & "if" a equiv 0 pmod(p),
                1 & "if" a equiv.not 0 pmod(p) "and" a "is a quadratic residue" mod p,
                -1 & "if" a equiv.not 0 pmod(p) "and" a "is a quadratic non-residue" mod p.
              )
  $
]

#proposition[Properties of Legendre Symbol][
  Let $p$ be an odd prime number and $a,b in ZZ$ be integers. Then the following properties hold:

  + $((a b) / p) = (a / p) (b / p)$. That is, the Legendre symbol is a completely multiplicative function.

  + $(a^2 / p) = 1$ for all $a in ZZ$.

  + $(a / p) = 0$ if and only if $p divides a$.
]

#theorem[Law of Quadratic Reciprocity][
  Let $p$ and $q$ be distinct odd prime numbers. Then the following statements hold:

  + The law of quadratic reciprocity:
    $
      (p / q) (q / p) = (-1)^( ((p-1)(q-1)) / 4 ).
    $

  + The first supplement to the law of quadratic reciprocity:
    $
      ( (-1) / p ) = (-1)^( (p - 1) / 2 ) = cases(
        1 & "if" p equiv 1 pmod(4),
        -1 & "if" p equiv 3 pmod(4).
      )
    $

  + The second supplement to the law of quadratic reciprocity:
    $
      ( (2) / p ) = (-1)^( (p^2 - 1) / 8 ) = cases(
        1 & "if" p equiv 1 "or" 7 pmod(8),
        -1 & "if" p equiv 3 "or" 5 pmod(8).
      )
    $
]

With the Legendre symbol, for odd prime number $p$, we can describe the structure of $FF_p (sqrt(a)):=FF_p [x]\/(x^2-a)$ as follows
$
  FF_p (sqrt(a)) tilde.equiv cases(
    FF_p & "if" (a / p) = 1",",
    FF_(p^2) & "if" (a / p) = -1.
  )
$

== $p$-adic Numbers

=== $p$-adic Integers
#definition[$p$-adic Integer][
  Let $p$ be a prime number. The $p$-adic integer topological ring is defined as
  $
    ZZ_p = projlim(n) ZZ \/ p^n ZZ.
  $
  The universal property of $ZZ_p$ is given by the following commutative diagram

  #commutative_diagram(
    $
      &&&&&G edge("d", "-->") edge("ddr", "->")\
      &&&&&ZZ_p edge("d", pi_m, "->") edge("dr", "->") edge("dll", "->") edge("dllll", "->") edge("dlllll", "->") \
      ZZ\/p ZZ edge("<-")
      & ZZ\/p^2 ZZ edge("<-")
      & dots.c.h edge("<-")
      & ZZ\/p^n ZZ edge("<-")
      & dots.c edge("<-")
      & ZZ\/p^m ZZ edge("<-")
      & dots.c
    $,
  )
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

#proposition[Properties of $ZZ_p$][
  - $ZZ_p$ is a principal ideal domain. Ideals of $ZZ_p$ can be classified as

    + $p^n ZZ_p$ for some $n in bb(Z)_(>= 0)$,

    + ${0}$,

  - $ZZ_p$ is a local ring with maximal ideal $p ZZ_p$. The residue field of $ZZ_p$ is isomorphic to the finite field $FF_p$
    $
      ZZ_p \/ p ZZ_p tilde.equiv FF_p.
    $
]



=== $p$-adic Valuation
#definition[$p$-adic Valuation][
  Let $p$ be a prime number. The #strong[$p$-adic valuation] is defined as
  $
    v_p : bb(Q) & arrow.r.long bb(Z) union {oo} \
          a / b & arrow.r.bar.long cases(
                    oo & " if" a = 0\,,
                    max { n in bb(Z) divides p^n divides a } - max { n in bb(Z) divides p^n divides b } & " if" a eq.not 0 .
                  )
  $
]


The #strong[$p$-adic absolute value] is defined as
$
  lr(|thin dot.op thin|)_p : bb(Q) & arrow.r.long bb(R)_(gt.eq 0) \
                                 x & arrow.r.bar.long cases(
                                       0 & " if" a = 0\,,
                                       p^(- v_p (x)) & " if" x eq.not 0 .
                                     )
$

#proposition[Properties of $p$-adic Valuation][
  Let $p$ be a prime number.
  + If $n in ZZ$ is an interger, then
    $
      p^N divides n <==> n equiv 0 pmod(p^N) <==> v_p (n) >= N <==> abs(n)_(p) <= p^(-N).
    $
  + If $n in ZZ$ is an integer, then
    $
      p^N divides n "and" p^(N+1) divides.not n <==> v_p (n) = N <==> abs(n)_(p) = p^(-N).
    $
]

#definition[Global Field][
  A #strong[global field]#index("global field") is a field isomorphic to one of the following:

  - a #strong[number field]#index("global field", "number field"): finite extension of $bb(Q)$,

  - a #strong[function field] over a finite field $bb(F)_q$#index("global field", "function field"): finite extension of $bb(F)_q (t)$.
]

#definition[Local Field][
  A #strong[local field] #index("local field") is a field isomorphic to one of the following:

  - (Character zero): $bb(R)$, $bb(C)$ or a finite extension of $bb(Q)_p$,

  - (Character $p > 1$): the field of formal Laurent series
    $bb(F)_q ((t))$, where $q = p^n$.
]

=== Topology of $QQ_p$
#example[Open Ball in $QQ_p$][
  Let $p$ be a prime number. For any $a in QQ_p$ and $r in bb(R)_(gt 0)$, the #strong[open ball] of $a$ of radius $r$ in $QQ_p$ is given by
  $
    B_(r) (a) = { x in QQ_p mid(|) abs(x - a)_p < r }.
  $
  If $r=p^(-n)$ for some $n in bb(Z)$, then we have
  $
    B_(p^(-n)) (a) = { x in QQ_p mid(|) abs(x - a)_p < p^(-n) }= { x in QQ_p mid(|) v_p (x - a) > n }= a + p^(n+1) ZZ_p.
  $
  Note that $n(r)=ceil(-log_p r)$ is the smallest integer such that $p^(-n(r)) <= r$. Thus the open ball $B_(r) (a)$ can be written as
  $
    B_(r) (a) =B_(p^(-n(r))) (a)= a + p^(n(r)+1) ZZ_p.
  $
  Open ball in $QQ_p$ is also a closed ball because
  $
    B_(p^(-n)) (a) = { x in QQ_p mid(|) abs(x - a)_p <= p^(-(n+1)) }= overline(B_(p^(-(n+1))) (a)).
  $
]

#lemma[All Open Balls in $QQ_p$ are Homeomorphic][
  All open balls in $QQ_p$ are homeomorphic.
]<open-balls-in-QQp-are-homeomorphic>
#proof[
  It is sufficient to show that for any $a in QQ_p$ and $n in bb(Z)$, the open ball $B_(p^(-n)) (a)$ is homeomorphic to $B_(1) (0)=p bb(Z)_p$. Consider the map
  $
    phi:B_(1) (0) & --> B_(p^(-n)) (a) \
                x & mapsto.long a + p^n x.
  $
  It is well-defined because for any $x = limits(sum)_(i = 1)^(oo) a_i p^i in B_(1) (0)$, we have
  $
    phi(x) = a + p^n sum_(i = 1)^(oo) a_i p^i = a + p^(n+1) sum_(i = 1)^(oo) a_i p^(i-1) in B_(p^(-n)) (a).
  $
  And we can verify the inverse map of $phi$ is given by
  $
    phi^(-1):B_(p^(-n)) (a) & --> B_(1) (0) \
                          y & mapsto.long p^(-n) (y - a).
  $
  The continuity of $phi$ and $phi^(-1)$ follows from the fact that the addition and multiplication are continuous in $QQ_p$.
]

#proposition[Open Ball in $QQ_p$ is Compact][
  For any $a in QQ_p$ and $r in bb(R)_(gt 0)$, the open ball $B_(r) (a)$ in $QQ_p$ is compact.
]
#proof[
  According to @open-balls-in-QQp-are-homeomorphic, it is sufficient to show that $B_(p^(-1)) (0)=bb(Z)_p$ is compact. Given any $epsilon>0$, we can find $n in bb(Z)_(gt 0)$ such that $p^(-n) < epsilon$. Then we have
  $
    bb(Z)_p = union.big_(k = 0)^(p^(n+1) - 1) (k + p^(n+1) bb(Z)_p) = union.big_(k = 0)^(p^(n+1) - 1) B_(p^(-n)) (k) ==> bb(Z)_p = union.big_(k = 0)^(p^(n+1) - 1) (B_(epsilon) (k) inter bb(Z)_p).
  $
  This shows that $bb(Z)_p$ can be covered by a finite number of open balls of radius $epsilon$. Thus $bb(Z)_p$ is totally bounded. Since $bb(Z)_p$ is also closed in $QQ_p$, it is complete. A complete and totally bounded metric space is compact. Therefore, $bb(Z)_p$ is compact and we complete the proof.
]

=== Harr Measure on $QQ_p$


#example[Haar Measure on $QQ_p$][
  Let $p$ be a prime number. There exists a unique (up to a scalar multiple) Haar measure $mu$ on the additive group $QQ_p$ such that $mu(ZZ_p)=1$. And we have
  $
    mu(a + p^n ZZ_p) = p^(-n), quad forall a in QQ_p,med n in ZZ.
  $
  where
  $
    a + p^n ZZ_p = overline(B_(p^(-n)) (a)) = { x in QQ_p mid(|) abs(x - a)_p <= p^(-n) }
  $
  is a closed ball in $QQ_p$.
]

#example[][
  For any $n in bb(Z)_(>= 0)$, we have
  $
    mu(p^n ZZ_p^times) = p^(-n) (1 - p^(-1)).
  $
]
#proof[
  Note
  $
    p^n ZZ_p^times & = { x in ZZ_p mid(|) abs(x)_p = p^(-n) } \
    & ={ x in ZZ_p mid(|) abs(x)_p <= p^(-n) }-{ x in ZZ_p mid(|) abs(x)_p <= p^(-n-1) } \
    & = p^n ZZ_p - p^(n+1) ZZ_p \
    &= union.sq.big_(k = 0)^(p-1) (k p^n + p^(n+1) ZZ_p) -  p^(n+1) ZZ_p \
    & = ( p^n + p^(n+1)ZZ_p ) union.sq (2 p^n + p^(n+1) ZZ_p ) union.sq dots.h.c union.sq ((p-1) p^n+ p^(n+1) ZZ_p ).
  $
  We have
  $
    mu(p^n ZZ_p^times) = mu(p^n ZZ_p) - mu(p^(n+1) ZZ_p) = p^(-n) - p^(-n-1)= p^(-n) (1 - p^(-1)).
  $
]

#example[Integral on $ZZ_p-{0}$][
  The complex function
  $
    f: ZZ_p-{0} & --> bb(C) \
              x & mapsto.long abs(x)_p^s
  $
  is continuous and accordingly Haar measurable. Moreover, $f in L^1(ZZ_p-{0})$ if and only if $op("Re")(s) > -1$. In this case, we have
  $
    integral_(ZZ_p-{0}) abs(x)_p^s dif x = (1 - p^(-1)) / (1 - p^(-s-1)) , quad forall op("Re")(s) > -1.
  $
]
#proof[
  Since
  $
    ZZ_p-{0} = union.sq.big_(n = 0)^(oo) (p^n ZZ_p^times) ,
  $
  we have
  $
    norm(f)_(L^1) & =integral_(ZZ_p-{0}) abs(abs(x)_p^s) dif x \
    & = integral_(ZZ_p-{0}) abs(x)_p^(op("Re")(s)) dif x \
    & = sum_(n = 0)^(oo) integral_(p^n ZZ_p^times) abs(x)_p^(op("Re")(s)) dif x \
    & = sum_(n = 0)^(oo) p^(-n op("Re")(s)) mu(p^n ZZ_p^times) \
    &= sum_(n = 0)^(oo) p^(-n op("Re")(s)) mu(p^n ZZ_p^times)
    & = (1 - p^(-1)) sum_(n = 0)^(oo) p^(-n s).
  $
]

=== Structure of $QQ_p^times$

#proposition[][
  The group $QQ_p^times$ is isomorphic to $p^ZZ times ZZ_p^times$ via the continous homomorphism
  $
    phi: QQ_p^times & -->^(tilde) p^ZZ times ZZ_p^times \
                  x & mapsto.long (p^(v_p (x)), p^(-v_p (x))x) \
              p^n u & arrow.bar.long.l (p^n, u)
  $
  where $p^ZZ= { p^n mid(|) n in bb(Z) }$ is endowed with the discrete topology and $ZZ_p^times$ is endowed with the subspace topology induced from $QQ_p^times$.

  Through the topological group isomorphism
  $
    p^ZZ & -->^(tilde) ZZ \
     p^n & mapsto.long n \
  $
  we have $QQ_p^times tilde.equiv ZZ times ZZ_p^times$ as topological groups.
]
#proof[
  - _Well‐definedness_. For any $x in QQ_p^times$, we have
    $
      v_p (p^(-v_p (x))x)=v_p (x) - v_p (x) = 0 ==> p^(-v_p (x))x in ZZ_p^times.
    $

  - _Group homomorphism_. For any $x,y in QQ_p^times$, we have
    $
      phi(x y) & = (p^(v_p (x y)), p^(-v_p (x y)) x y) \
               & = (p^(v_p (x) + v_p (y)), p^(-v_p (x) - v_p (y)) x y) \
               & = (p^(v_p (x)), p^(-v_p (x)) x)(p^(v_p (y)), p^(-v_p (y)) y) \
               & = phi(x) phi(y).
    $

  - _Inverse and bijectivity_. Define $psi: (p^n, u) & mapsto p^n u$. For any $x in QQ_p^times$, we have
    $
      psi(phi(x)) = psi(p^(v_p (x)), p^(-v_p (x)) x) = p^(v_p (x)) p^(-v_p (x)) x = x.
    $
    Conversely, for any $(p^n, u) in p^ZZ times ZZ_p^times$, we have
    $
      phi(psi(p^n, u)) = phi(p^n u) = (p^(v_p (p^n u)), p^(-v_p (p^n u)) p^n u) = (p^n, p^(-n) p^n u) = (p^n, u).
    $
    Thus $psi$ is the inverse of $phi$ and $phi$ is bijective.

  - _Continuity_. To show that $phi$ is continuous, it is sufficient to show that the two coordinates of $phi$ are continuous.The first coordinate $x arrow.bar p^(v_p (x))$ factors as
    $
      QQ_p^times stretch(->, size: #(150% + 15pt))^(v_p) ZZ stretch(->, size: #150%)^(n arrow.bar p^n) p^ZZ.
    $
    Since $v_p$ is continuous and $n arrow.bar p^n$ is homeomorphism between two discrete spaces, the first coordinate is continuous. The second coordinate $x arrow.bar p^(-v_p (x)) x$ is continuous because it is the product of two continuous functions: $x arrow.bar p^(-v_p (x))$ and $x arrow.bar x$.
]

=== Structure of $ZZ_p^times$
#example[Unit Group of $ZZ_p$][
  The unit group of $ZZ_p$ is given by
  $
    ZZ_p^times & = { x in ZZ_p mid(|) x = a_0 + a_1 p + dots.h.c + a_n p^n + dots.h.c " and" a_0 != 0} \
               & = { x in ZZ_p mid(|) abs(x)_p=1 } \
               & = { x in ZZ_p mid(|) v_p (x) = 0 }
  $
  In other words, the units of $ZZ_p$ are precisely those $p$-adic integers whose first digit in base-$p$ form is non-zero.
]<unit-group-of-ZZp>

#lemma[Hensel's Lemma][
  Let $p$ be a prime number and $f(X) in ZZ_p [X]$ be a polynomial. If $a in ZZ_p$ satisfies
  $
    f(a) equiv 0 med(mod p) " and " f'(a) equiv.not 0 med(mod p) .
  $
  Then there exists a unique $u in ZZ_p$ such that
  $
    f(u) = 0 " and " u equiv a med(mod p).
  $
]<hensel-lemma>

#proposition[Teichmüller Lift][
  Let $p$ be a prime number. Let
  $
    pi: ZZ_p^times & --> (ZZ\/ p ZZ)^times \
                 x & mapsto.long x mod p
  $
  be the projection map. Then the following statements hold:

  + There exists a unique group homomorphism $omega:(ZZ\/ p ZZ)^times -> ZZ_p^times$ such that $pi compose omega = id$.

  + $omega$ is an injective continuous group homomorphism.

  + The image of $omega$ is given by
    $
      omega((ZZ\/ p ZZ)^times)= mu_(p-1)(ZZ_p^times) = { x in ZZ_p^times mid(|) x^(p-1) = 1 }.
    $

  This map $omega$ is called the *Teichmüller lift*.
]<Teichmüller-lift>
#proof[
  + - _Existence_. Consider the polynomial $f(X) = X^(p-1) - 1 in ZZ_p [X]$. For any $overline(a) in (ZZ\/ p ZZ)^times$, where $a in ZZ$ is an integer such that $p divides.not a$, we have
      $
        f(a) = a^(p-1) - 1 equiv 0 med(mod p).
      $
      Note $f'(X) = (p-1) X^(p-2)$. It follows that
      $ f'(a) = (p-1) a^(p-2)= -a^(p-2) equiv.not 0 med(mod p) $ because $a^(p-2) in (ZZ\/ p ZZ)^times$. By #link(<hensel-lemma>)[
        Hensel's lemma], there exists a unique $u in ZZ_p^times$ such that
      $
        f(u) = u^(p-1) - 1 = 0 quad " and " quad u equiv a med(mod p).
      $
      Define $omega(overline(a)) := u$. Suppose $overline(a)=overline(b)$. Then we can obtain that there exists unique $v in ZZ_p^times$ such that
      $
        f(v) = v^(p-1) - 1 = 0 quad " and " quad v equiv b med(mod p).
      $
      Note $v equiv b equiv a med(mod p)$. By #link(<hensel-lemma>)[
        Hensel's lemma], $u=v$, which implies $omega(overline(a)) = omega(overline(b))$. Thus we have a well-defined map
      $
        omega:(ZZ\/ p ZZ)^times & --> ZZ_p^times \
                    overline(a) & mapsto.long omega(overline(a))
      $
      where $omega(overline(a))$ is the unique solution of $f(X) = 0$ such that $X equiv a med(mod p)$.
      For any $overline(a) in (ZZ\/ p ZZ)^times$, we have
      $
        pi(omega(overline(a))) = pi(u) = u mod p = a mod p = overline(a),
      $
      which implies $pi compose omega = id$.

      For any $overline(a), overline(b) in (ZZ\/ p ZZ)^times$, we have
      $
        f(omega(overline(a)) omega(overline(b))) = (omega(overline(a)) omega(overline(b)))^(p-1) - 1
        = omega(overline(a)^(p-1)) omega(overline(b)^(p-1)) - 1
        = 1 - 1 = 0
      $
      and
      $
        omega(overline(a)) omega(overline(b)) equiv a b med(mod p).
      $
      But by definition of $omega$, we have $omega(overline(a)) omega(overline(b))=omega(overline(a b))$. This shows that $omega$ is a group homomorphism.

    - _Uniqueness_. Suppose there exists another group homomorphism $omega':(ZZ\/ p ZZ)^times -> ZZ_p^times$ such that $pi compose omega' = id$. Then for any $overline(a) in (ZZ\/ p ZZ)^times$, we have
      $
        pi(omega'(overline(a))) = overline(a) = pi(omega(overline(a)))
        ==> omega'(overline(a)) equiv omega(overline(a)) equiv a med(mod p).
      $
      Note
      $
        omega'(overline(a))^(p - 1)=omega'(overline(a)^(p - 1))=omega'(overline(1))=1==> f(omega'(overline(a))) = omega'(overline(a))^(p - 1) - 1 = 0.
      $
      By #link(<hensel-lemma>)[
        Hensel's lemma], the solution of $f(X) = 0$ such that $X equiv a med(mod p)$ is unique. Thus we have $omega(overline(a)) = omega'(overline(a))$ for all $overline(a) in (ZZ\/ p ZZ)^times$. Therefore, $omega$ is unique.

  + The injectivity of $omega$ follows from the fact that $pi compose omega = id$, i.e. $omega$ has a left inverse. The continuity of $omega$ follows from the fact that any map from a discrete space is automatically continuous.

  + It is straightforward to check
    $
      omega((ZZ\/ p ZZ)^times) subset.eq mu_(p-1)(ZZ_p^times) ={ x in ZZ_p^times mid(|) x^(p-1) = 1 }.
    $
    Since $omega$ is injective, $abs(mu_(p-1)(ZZ_p^times)) >= abs(omega((ZZ\/ p ZZ)^times))>=|(ZZ\/ p ZZ)^times|=p-1.$
    The number of roots of a non-zero polynomial over commutative integral domain is at most its degree. So $abs(mu_(p-1)(ZZ_p^times))<=p - 1$, which forces $abs(mu_(p-1)(ZZ_p^times))=p - 1$. Thus $omega: (ZZ\/ p ZZ)^times->mu_(p-1)(ZZ_p^times)$ is a bijection and we have
    $
      omega((ZZ\/ p ZZ)^times) = mu_(p-1)(ZZ_p^times).
    $
]

#proposition[][
  Let
  $
    pi: ZZ_p^times & --> (ZZ\/ p ZZ)^times \
                 x & mapsto.long x mod p
  $
  be the projection map. Then $pi$ is a continuous surjective group homomorphism with kernel
  $
    ker pi =1+p ZZ_p={1 + p x in ZZ_p^times mid(|) x in ZZ_p}.
  $
  This gives an exact sequence of topological groups
  $
    1 & --> 1 + p ZZ_p & --> ZZ_p^times & -->^(pi) (ZZ\/ p ZZ)^times & --> 1.
  $
  Let
  $
    omega: (ZZ\/ p ZZ)^times & --> ZZ_p^times
  $
  be the #link(<Teichmüller-lift>)[Teichmüller lift]. If satisfies $pi compose omega = id$ and the image of $omega$ is given by
  $
    omega((ZZ\/ p ZZ)^times)= mu_(p-1)(ZZ_p^times) = { x in ZZ_p^times mid(|) x^(p-1) = 1 }.
  $
  Thus we have the following isomorphism of topological groups
  $
    ZZ_p^times tilde.equiv mu_(p-1)(ZZ_p^times) times (1 + p ZZ_p).
  $
]
#proof[
  - _Kernel of $pi$_. For any $1+p x in ZZ_p^times$, where $x in ZZ_p$, we have
    $
      pi(1 + p x) = (1 + p x) mod p = 1.
    $
    Thus the $1+p ZZ_p subset.eq ker pi$. Conversely, for any $x = limits(sum)_(i = 0)^(oo) a_i p^i in ker pi$, we have
    $
      pi(x)=a_0=1.
    $
    Thus $x = 1 + p x'$, where $x' = limits(sum)_(i = 1)^(oo) a_i p^(i-1) in ZZ_p$, which shows $ker pi subset.eq 1 + p ZZ_p$. Therefore, it follows that $ker pi = 1 + p ZZ_p$.

  - _Decomposition_. Since the exact sequence
    $
      1 & --> 1 + p ZZ_p & --> ZZ_p^times & -->^(pi) (ZZ\/ p ZZ)^times & --> 1
    $
    is split, we have
    $
      ZZ_p^times tilde.equiv (ZZ\/ p ZZ)^times times (1 + p ZZ_p) tilde.equiv mu_(p-1)(ZZ_p^times) times (1 + p ZZ_p).
    $

]

#proposition[][
  Let
  $
    pi_k: ZZ_p^times & --> (ZZ\/ p^k ZZ)^times \
                   x & mapsto.long x mod p^k
  $
  be the reduction modulo $p^k$ map. Then $pi_k$ is a continuous surjective group homomorphism with kernel
  $
    ker pi_k =1+p^k ZZ_p={1 + p^k x in ZZ_p^times mid(|) x in ZZ_p}.
  $
  This gives an exact sequence of topological groups
  $
    1 & --> 1 + p^k ZZ_p & --> ZZ_p^times & -->^(pi_k) (ZZ\/ p^k ZZ)^times & --> 1.
  $
  And we have the following isomorphism of topological groups
  $
    theta:(ZZ\/ p^k ZZ)^times & -->^(tilde) ZZ_p^times \/ (1 + p^k ZZ_p) \
                  overline(a) & mapsto.long a( 1 + p^k ZZ_p) = a + p^k ZZ_p.
  $
]
#proof[
  - _Continuity of $pi_k$_. Since the topology of $(ZZ\/ p^k ZZ)^times$ is discrete, it suffices to show the preimage of any singleton subset of $(ZZ\/ p^k ZZ)^times$ is open in $ZZ_p^times$.


  Suppose $overline(a)in (ZZ\/ p^k ZZ)^times$, where $a in ZZ$ is an integer such that $gcd(a, p)=1$. Then $a$ regarded a $p$-adic integer satisfies $a in ZZ_p^times$.

  For any $x in ZZ_p^times$, we have
  $
    pi_k \( x \) = overline(a) & <==> x equiv a med \( mod med p^k \) \
                               & <==> a^(- 1) x equiv 1 med \( mod med p^k \) \
                               & <==> a^(- 1) x in 1 + p^k bb(Z)_p \
                               & <==> x in a( 1 + p^k bb(Z)_p) \
                               & <==> x in a + p^k bb(Z)_p.
  $
  Hence $pi_k^(-1) ({overline(a)})=a+ p^k bb(Z)_p$.

]

== Profinite Completion of $ZZ$
The #strong[profinite completion] of $ZZ$ is defined as
$
  hat(ZZ) = lim_(leftarrow_n) ZZ \/ n ZZ.
$


== Adeles and Ideles

#definition[Adele Ring of Global Field][
  Let $K$ be a global field. The #strong[adele ring] of $K$ is defined as the restricted product
  $
    bb(A)_(K) = product_(v in mono("pl")_K)^' K_v.
  $
  By the restricted product, we mean that $bb(A)_(K)$ is the subring of
  $product_(v in mono("pl")_K) K_v$ consisting of all elements $(x_v)_(v in mono("pl")_K)$ such that $|x_v| <= 1$ for all but finitely many $v in mono("pl")_K$. The topology on $bb(A)_(K)$ is given by define the basis of the form
  $
    product_(v in mono("pl")_K) U_v
  $
  where $U_v$ is an open subset of $K_v$ and
  $U_v = O_v$ for all but finitely many $v in mono("pl")_K^(op("fin"))$.
]

Adele ring of a global field is a locally compact topological ring.


#definition[Idele Group of Global Field][
  Let $K$ be a global field. The #strong[idele group] of $K$ as a group is defined as
  $
    bb(I)_(K) = bb(A)_(K)^times = op("GL")_1 (bb(A)_(K)).
  $
  The topology on $bb(I)_(K)$ is given by define the basis of the form
  $
    product_(v in mono("pl")_K) U_v
  $
  where $U_v$ is an open subset of $K_v^times$ and
  $U_v = O_v^times$ for all but finitely many $v in mono("pl")_K^(op("fin"))$.
]

Though $II_(K)$ is a subset of $AA_K$, the topology of $II_(K)$ is not the subspace topology induced from the $AA_K$.


#definition[Idelic Absolute Value][
  Let $K$ be a global field. The #strong[idelic absolute value] is defined as
  $
    lr(|thin dot.op thin|)_(bb(I)_(K)) : bb(I)_(K) & arrow.r.long bb(R)_(gt.eq 0) \
                         (x_v)_(v in mono("pl")_K) & arrow.r.bar.long product_(v in mono("pl")_K) lr(|x_v|_v)
  $
]

#proposition[Product Formula][
  Let $K$ be a global field. For any $x in K^times$, we have
  $
    lr(|x|_(bb(I)_(K))) = product_(v in mono("pl")_K) lr(|x_v|_v) = 1.
  $
]

=== Adele Ring of $QQ$

#definition[Adele Ring of $QQ$][
  The #strong[adele ring] #index("adele ring") of $QQ$ is defined as
  $
    bb(A)_(QQ) & = RR times attach(product_p, t: ') QQ_p \
               & = { (x_(oo),x_2,x_3,dots.c) in RR times product_p QQ_p mid(|) x_p in ZZ_p "for all but finitely many" p }.
  $
  The topology on $bb(A)_(QQ)$ is given by defining the basis of the form
  $
    U = U_(oo) times product_p U_p
  $
  where $U_v$ is an open subset of $QQ_v$ such that $U_p = ZZ_p$ for all but finitely many $p$.
]

#proposition[Properties of $bb(A)_(QQ)$][
  - $bb(A)_(QQ)$ is a locally compact topological ring.
]

#example[Diagonal Embedding $QQ arrow.r.hook bb(A)_(QQ)$][
  The diagonal embedding $QQ arrow.r.hook bb(A)_(QQ)$ is given by
  $
    x & mapsto.long (x, x, x, dots.c)
  $
  This map is a continuous and injective topological ring embedding. Therefore, we can identify $QQ$ with a subring of $bb(A)_(QQ)$.
]

Since $QQ$ embeds into $AA_QQ$, whenever we perform operations involving elements of $QQ$ and $AA_QQ$, we identify each rational number with its image in $AA_QQ$ under the diagonal embedding.

#example[Action of $bb(Q)$ on $bb(A)_(QQ)$][
  Since we can see $bb(Q)$ as a additive subgroup of $bb(A)_(QQ)$, we can consider the quotient group $bb(A)_(QQ)\/ bb(Q)$. This gives an action of $bb(Q)$ on $bb(A)_(QQ)$ as follows
  $
                     bb(Q) times bb(A)_(QQ) & --> bb(A)_(QQ) \
    (q, (x_(oo),x_2,x_3,dots.c,x_p,dots.c)) & mapsto.long (q + x_(oo), q + x_2, q + x_3, dots.c,q+x_p,dots.c).
  $

]
#proposition[Weak Approximation for Adeles][
  Let $p_1 , p_2 ,dots.c , p_n$ be
  distinct primes. Let $c_i in bb(Q)_(p_i)$ for each
  $i = 1 , 2 , dots.c , n$. Then for every $epsilon.alt > 0$, there
  exists an $alpha in bb(Q)$ such that

  $ abs(alpha - c_i)_(p_i) < epsilon.alt $

  for all $1 lt.eq i lt.eq n$. Furthermore, $alpha$ may be chosen so that
  for prime number $p in.not {p_1 , p_2 ,dots.c , p_n}$, we have
  $
    abs(alpha)_(p) <= 1 quad (1 <= i <= n).
  $
]<weak-approximation-for-adeles>
#proof[
  Let's first assume that $c_i in bb(Z)_(p_i)$ for all $i$. For any $epsilon>0$, there exists a positive integer $N$ such that
  $
    max_(1 <= i <= n) p_i^(-N) < epsilon.
  $
  Our goal is to find a rational number $alpha in QQ$ such that for each $i$, we have
  $
    abs(alpha - c_i)_(p_i) < p_i^(-N)
  $
  For each $i$, as $bb(Z)$ is dense in $bb(Z)_(p_i)$, we can find an integer $a_i$ such that
  $
    abs(a_i - c_i)_(p_i) < p_i^(-N).
  $
  By the the Chinese Remainder Theorem, we can find an integer $a in ZZ$ satisfies the following system of congruence equation
  $
    a equiv a_i pmod(p_i^N) quad (1 <= i <= n).
  $
  The solution $a$ is unique modulo $p_1^N p_2^N dots.h p_n^N$. Thus, we have
  $
    abs(a - c_i)_(p_i) = abs((a-a_i) + (a_i - c_i))_(p_i) <=max(abs(a-a_i)_(p_i), abs(a_i - c_i)_(p_i))<= p_i^(-N)< epsilon.
  $

  Now, we handle the general case where each $c_i$ is in $bb(Q)_(p_i)$. We can write each $c_i$ as
  $
    c_i = p_i^(-k_i)u_i, quad k_i in ZZ_(>=0), quad u_i in bb(Z)_(p_i)^times.
  $
  Let
  $
    M:= p_1^(k_1)p_2^(k_2) dots.c thin p_n^(k_n).
  $
  Then we can clear the local denominators by multiplying each $c_i$ by $M$
  $
    d_i:= M c_i= u_i in bb(Z)_(p_i).
  $
  Given any $epsilon>0$, define
  $
    delta:= min_(1 <= i <= n) (epsilon thin p_i^(-k_i)).
  $
  By the integral case of the weak approximation theorem, there exists an integer $b$ such that
  $
    abs(b - d_i)_(p_i) < delta quad (1 <= i <= n).
  $
  Let $alpha=b/M$. Thenfor each $i$ we have
  $
    abs(alpha - c_i)_(p_i) = abs(M^(-1)(b-d))_(p_i)= p^(k_i)abs(b-d_i)_(p_i)<p^(k_i)delta<= epsilon.
  $
  It is easy to see that the set of prime factors of denominator of $alpha$ is contained by ${p_1 , p_2 ,dots.c , p_n}$.
]

#proposition[Strong Approximation for Adeles][
  $A$ fundamental domain $D$ for the action of $bb(Q)$ on $bb(A)_(QQ)$  is given by
  $
    D & = {(x_oo \, x_2 \, x_3 \, dots.c) divides 0 lt.eq x_oo < 1 "and" x_p in bb(Z)_p "for all finite primes" p} \
      & = \[ 0 \, 1 \) times product_p bb(Z)_p .
  $

]
#proof[
  It is enough to show that every
  element in $bb(A)_(bb(Q))$ can be uniquely expressed as $( q , q , q , dots.c ) + d$ for
  $d in D$ and $q in bb(Q)$.

  Fix $x = (x_oo \, x_2 \, x_3 \, dots.c ) in bb(A)_(bb(Q))$. Apply @weak-approximation-for-adeles with $p_1 \, dots.h \, p_n$ being the finite set of primes
  such that $x_(p_i) in.not bb(Z)_(p_i) \, c_i = x_(p_i)$ and
  $epsilon.alt = 1$. We obtain $alpha in bb(Q)$ such that
  $
    abs(x_(p_i) - alpha)_(p_i) <= 1 quad (1 <= i <= n).
  $
  For any prime number $p$ not in the set $\{p_1 , p_2 ,dots.c , p_n\}$, we have $x_p in ZZ_p$ and
  $
    abs(x_p - alpha)_(p) <= max(abs(x_p)_(p), abs(alpha)_(p)) <= 1.
  $
  Thus we get
  $
    abs(x_p - alpha)_(p)<= 1
  $
  for each prime number $p$. Hence, we have
  $
    x_p - alpha - floor(x_oo - alpha) in bb(Z)_p
  $
  for all primes $p$ and
  $
    x_oo - alpha - floor(x_oo - alpha) in [ 0 , 1 ),
  $
  which means
  $
    (x_oo,x_2,x_3,dots.c) - (alpha+ floor(x_oo - alpha),alpha+ floor(x_oo - alpha),alpha+ floor(x_oo - alpha),dots.c) in D.
  $
  We have thus found
  $q := alpha + floor(x_oo - alpha) in bb(Q)$ and $d:=x-( q , q , q , dots.c ) in D$ such that

  $
    x=(x_oo,x_2,x_3,dots.c) = ( q , q , q , dots.c ) +d .
  $

  Next, we consider uniqueness. Suppose there exists $q' in bb(Q)$ and
  $d' in D$ such that
  $
    x = ( q' , q' , q' , dots.c )+d'.
  $
  This implies
  $
    ( q , q , q , dots.c ) - (q' , q' , q' , dots.c ) = d' - d.
  $
  So we have $q - q' in ZZ_p$ for all primes $p$, which means $q - q' in ZZ$.
  At the place $v=oo$ we must
  have
  $
    q - q' = d'-d in (- 1 , 1).
  $
  This forces $q - q' =0$ and $q = q'$.
]

=== Idele Group of $bb(Q)$

If we endow $bb(A)_(QQ)^times$ with the subspace topology induced from $bb(A)_(QQ)$, then the inverse operation $x arrow.r.bar x^(-1)$ is not continuous. Thus we need endow $bb(A)_(QQ)^times$ with a stronger topology to make the inverse operation continuous.

#definition[Idele Group of $bb(Q)$][
  The #strong[idele group] #index("idele group") of $bb(Q)$ is defined as
  $
    bb(I)_(QQ) = bb(A)_(QQ)^times = op("GL")_1 (bb(A)_(QQ))= { (x_(oo),x_2,x_3,dots.c) in AA_QQ mid(|) x_p in ZZ_p^times "for all but finitely many" p }.
  $
  The topology on $bb(I)_(QQ)$ is given by defining the basis of the form
  $
    U = U_(oo) times product_p U_p
  $
  where $U_v$ is an open subset of $QQ_v^times$ such that $U_p = ZZ_p^times$ for all but finitely many $p$.
]
$bb(A)_(QQ)^times$ is a locally compact Hausdorff topological group. The connected component of the identity of $bb(A)_(QQ)^times$ is $(RR_(>0),times)$, which is the multiplicative group of positive real numbers, regarded as a subgroup of $bb(A)_(QQ)^times$ through the diagonal embedding.



#example[Action of $bb(Q)^times$ on $bb(A)_(QQ)^times$][
  Since we can see $bb(Q)^times$ as a subgroup of $bb(A)_(QQ)^times$, we can consider the quotient group $bb(A)_(QQ)^times \/ bb(Q)^times$. This gives an action of $bb(Q)^times$ on $bb(A)_(QQ)^times$ as follows
  $
    bb(Q)^times times bb(A)_(QQ)^times & --> bb(A)_(QQ)^times \
          (q, (x_(oo),x_2,x_3,dots.c)) & mapsto.long (q x_(oo), q x_2, q x_3, dots.c).
  $
]

#example[Local Embedding $QQ_v^times arrow.r.hook bb(A)_(QQ)^times$][
  For each place $v$, the local embedding $i_v: QQ_v^times arrow.r.hook bb(A)_(QQ)^times$ is given by
  $
    i_v: QQ_v^times & --> AA_(QQ)^times \
                  x & mapsto.long (1, dots.c, 1,x,1, dots.c)
  $
  where $x$ is in the position for place $v$ and all other positions are $1$. This map is a continuous and injective topological group embedding.
]

#definition[Idele Class Group][
  The #strong[idele class group] #index("idele class group") of $bb(Q)$ is defined as $AA_(QQ)^times \/ bb(Q)^times$.
]




#proposition[Strong Approximation for the Idele $bb(A)_(QQ)^times$][
  A fundamental domain for the action of $bb(Q)^times$ on $bb(A)_(QQ)^times$ is given by
  $
    D & ={ (x_(oo),x_2,x_3,dots.c) in bb(A)_(QQ)^times mid(|) 0<x_oo < oo "and" x_p in ZZ_p^times "for all" p } \
      & =(0, oo) times product_p ZZ_p^times.
  $
  Here $D subset.eq bb(A)_(QQ)^times$ is a fundamental domain for the action of $bb(Q)^times$ on $bb(A)_(QQ)^times$ means that for any $x in bb(A)_(QQ)^times$, there exists a $q in bb(Q)^times$ and $d in D$ such that $x = q d$, and the choice of $d$ is unique.

  We have decomposition
  $
    bb(A)_(QQ)^times = union.big_(q in bb(Q)^times ) q D
  $
  which satisfies
  $
    q_1 D != q_2 D ==> q_1 D inter q_2 D = emptyset.
  $
]
#proof[
  It is enough to show that every element in $bb(A)_(bb(Q))^times$ can be uniquely expressed as $q d$ for $d in D$ and $q in bb(Q)$.

  Fix $x = (x_oo \, x_2 \, x_3 \, dots.c ) in bb(A)_(bb(Q))$. Let
  $
    q := op("sgn")(x_oo) product_(p ) p^(v_p (x_p)) in bb(Q)^times.
  $
  $q$ is well-defined because $x_p in ZZ_p^times$ for all but finitely many $p$, which is equivalent to saying that $v_p (x_p) = 0$ for all but finitely many $p$.

  For any prime number $p$, we have
  $
    abs(q)_p = p^(-v_p (q)) = p^(-v_p (x_p)) = abs(x_p)_p==> abs(q^(-1) x_p)_p = 1.
  $
  Hence, we have
  $
    q^(-1) x_p in ZZ_p^times
  $
  for all primes $p$ and
  $
    q^(-1) x_oo in (0, oo),
  $
  which means
  $
    q^(-1)x=(q^(-1) x_oo, q^(-1) x_2, q^(-1) x_3, dots.c) in D.
  $
  We have thus found $q in bb(Q)^times$ and $d:=q^(-1) x in D$ such that
  $
    x= (q, q, q, dots.c) d=q d.
  $
  Next, we consider uniqueness. Suppose there exists $q' in bb(Q)^times$ and
  $d' in D$ such that
  $
    x = q' d'.
  $
  This implies
  $
    q/q' = d'/d.
  $
  So we have $q/q' in ZZ_p^times$ for all primes $p$, which implies $abs(q/q')=1$ by product formula. At the place $v=oo$ we must have
  $
    q/q' = d'/d in (0, oo).
  $
  This forces $q/q' =1$ and $q = q'$.

]

#pagebreak()

= _L_-Functions

== Dirichlet Charater

#definition[Euler's Totient Function][
  The #strong[Euler's totient function] is defined as
  $
    phi : bb(N) & arrow.r bb(N) \
              n & arrow.r.bar lr(|{a in bb(N) divides 1 lt.eq a lt.eq n , (a , n) = 1}|) .
  $
]

#proposition[Euler's Product Formula][
  For any $n in bb(N)$, we have the #strong[Euler's product formula] #index("Euler's product formula")
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

#proposition[Structure of $(bb(Z) \/ n bb(Z))^(times)$][
  For any integer $n >=2$, the multiplicative group of integers modulo $n$
  $ (bb(Z) \/ n bb(Z))^times= {a in bb(Z) \/ n bb(Z) mid(|) (a , n) = 1} $ is an abelian group of order $phi (n)$. The structure of $(bb(Z) \/ n bb(Z))^times$ is given by the following classification:

  + $n=p^k$ is an odd prime: $(bb(Z) \/ n bb(Z))^times tilde.equiv upright(C)_(p^(k-1)(p-1))$ is cyclic of order $p^k-p^(k-1)$. $(bb(Z) \/ n bb(Z))^times$ has $phi(p^k-p^(k-1))$ generators.

  + $n=2$: $(bb(Z) \/ 2 bb(Z))^times ={1}$ is isomorphic to trivial group.

  + $n=2^k$ for $k >= 2$:
    $
      (bb(Z) \/ 2^k bb(Z))^times=angle.l -1 angle.r times angle.l 5 angle.r={1, -1} times {1, 5, 5^2, dots.c, 5^(2^(k-2)-1)} tilde.equiv upright(C)_2 times upright(C)_(2^(k-2))
    $
    has order $2^(k-1)$.

  + $n=p_1 p_2 dots.c thin p_r$ is not a power of $2$:
    $
      (bb(Z) \/ n bb(Z))^times tilde.equiv (bb(Z) \/ p_1 bb(Z))^times times (bb(Z) \/ p_2 bb(Z))^times times dots.c times (bb(Z) \/ p_r bb(Z))^times.
    $


]


#definition[Dirichlet Character][
  Let $m$ be a positive integer. Given any group homomorphism
  $chi_m^star : (bb(Z) \/ m bb(Z))^times arrow.r bb(C)^times$, we can define a
  function $chi_m : bb(Z) arrow.r bb(C)$ by
  $
    chi_m (a) & =chi_m^star ([a])bold(1)_([a] in (bb(Z) \/ m bb(Z))^times) \
              & =
                cases(
                  0 & upright(" if") [a] in.not (bb(Z) \/ m bb(Z))^times & upright(" i.e. ") (a , m) eq.not 1,
                  chi_m^star ([a]) & upright(" if") [a] in (bb(Z) \/ m bb(Z))^times & upright(" i.e. ") (a , m) = 1
                )
  $
  Such function $chi_m$ is called a #strong[Dirichlet character modulo
    $m$]. #index("Dirichlet character")
]
#remark[
  We can switch between $chi_m$ and $chi_m^star$ according to the following relation
  $
    chi_m^star ([a]) & = chi_m (a), \
           chi_m (a) & = chi_m^star ([a]) bold(1)_([a] in (bb(Z) \/ m bb(Z))^times).
  $
]



#proposition[Properties of Dirichlet Character][
  + $chi_m : bb(Z) arrow.r bb(C)$ preserves multiplication: for any $a , b in bb(Z)$, #h(1fr)
    $
      chi_m (a b) = chi_m (a) chi_m (b).
    $
  + $chi_m$ has a period of $m$: for any $a in bb(Z)$,
    $
      chi_m (a + m) = chi_m (a).
    $
  + $chi_m (a)^phi(m) = 1$ for any $a in bb(Z)$, which implies
    $
      chi_m (a) in mu_(phi(m))= {z in bb(C) mid(|) z^phi(m) = 1}={zeta_phi(m)^(k) mid(|) zeta_phi(m) =e^(2pi i \/ phi(m)),k = 0, 1, dots.c, phi(m) - 1}.
    $
]

#example[Explicit Construction of Dirichlet Character of Modulus $p^k$][
  Suppose $q=p^k$ where $p$ is an odd prime. We can give an explicit construction of $(bb(Z) \/ q bb(Z))^times$. Suppose $g_q$ is a primitive root modulo $q$, or equivalently, a generator of $(bb(Z) \/ q bb(Z))^times$. Then for any $a in bb(Z)$, we can define a function $v_q (a)$ by
  $
    a equiv g_q^(v_q (a)) med mod med q, quad 0 <= v_q (a) < phi(q).
  $
  Note $chi_q^star in op("Hom")_(sans("Ab"))((bb(Z) \/ q bb(Z))^times,CC^times)$ is totally determined by $chi_q^star (g_q)$. To define a Dirichlet character modulo $q$, we can first define
  $
    chi_(q,r)^star (g_q) = zeta_(phi(q))^(v_q (r))
  $
  and then extend it to a function $chi_(q,r): bb(Z) -> bb(C)$ by

  $
    chi_(q,r) (a) = cases(
      0 & upright(" if") [a] in.not (bb(Z) \/ m bb(Z))^times & upright(" i.e. ") (a , q) eq.not 1\
      zeta_(phi(q))^(v_q (r)v_q (a)) & upright(" if") [a] in (bb(Z) \/ m bb(Z))^times & upright(" i.e. ") (a , q) = 1
    )
  $
]

#definition[Multiplication of Dirichlet Characters][
  Let $chi_m$ and $chi_m^'$ be two Dirichlet characters modulo $m$. The #strong[multiplication] of $chi_m$ and $chi_n$ is defined as
  $
    (chi_m chi_m^') (a) := chi_m (a) chi_m^' (a)
  $
  for any $a in bb(Z)$.
]

#definition[Principal Dirichlet Character][
  The #strong[principal Dirichlet character modulo $m$]#index("Dirichlet Character", "principal") is the simplest
  Dirichlet character defined by
  $
    chi_(m,1) (a) = cases(
      0 & upright(" if") [a] in.not (bb(Z) \/ m bb(Z))^times & upright(" i.e. ") (a , q) eq.not 1 \
      1 & upright(" if") [a] in (bb(Z) \/ m bb(Z))^times     &      upright(" i.e. ") (a , q) = 1
    )
  $
  This character is also called the *trivial character*#index("Dirichlet Character", "trivial").
]


Suppose $chi_m^star: (bb(Z) \/ m bb(Z))^times -> bb(C)^times$ is a Dirichlet character modulo $m$. For any $n in bb(Z)_(>0)$, by composing $chi_m^star$ and the natural projection $pi:(bb(Z) \/ n m bb(Z))^times -> (bb(Z) \/ m bb(Z))^times$ as follows
#commutative_diagram(
  $
    (bb(Z) \/ n m bb(Z))^times edge("d", "->>", pi) edge(->, chi_(n m)^star) & CC^times \
               (bb(Z) \/ m bb(Z))^times edge("ru", "->", chi_m^star, #right)
  $,
)
#[#set par(first-line-indent: 0em)
  we can define a Dirichlet character modulo $n m$ by
  $
    chi_(n m)^star ([a]) := chi_m^star (pi([a])),
  $
  or equivalently
  $
    chi_(n m) (a) := chi_m (a) bold(1)_([a] in (bb(Z) \/ n m bb(Z))^times).
  $
  In this case we say $chi_(m)^star$ *induces* $chi_(n m)^star$. If a Dirichlet character cannot factor through any projection $pi$, then it is called a primitive Dirichlet character. This brings us to the following definition.
]


#definition[Primitive Dirichlet Character][
  A Dirichlet character $chi_m$ is called a #strong[primitive Dirichlet character] #index("Dirichlet Character", "primitive") if it cannot be induced by any Dirichlet character $chi_d:(bb(Z) \/ d bb(Z))^times -> CC^(times)$ with $d divides m$ , that is, it cannot be factored as
  #commutative_diagram(
    $
      (bb(Z) \/ m bb(Z))^times edge("d", "->>", pi, #right) edge(->, chi_(m)^star) & CC^times \
                     (bb(Z) \/ d bb(Z))^times edge("ru", "->", chi_d^star, #right)
    $,
  )
  through projection $pi:(bb(Z) \/ m bb(Z))^times -> (bb(Z) \/ d bb(Z))^times$ for any integer $d > 1$ and any Dirichlet character $chi_d^star$ modulo $d$.
  If $chi_m$ is not primitive, then it is said to be *imprimitive*#index("Dirichlet Character", "imprimitive").
]


#definition[Conductor of Dirichlet Character][
  Let $chi_m$ be a Dirichlet character modulo $m$. We say $q$ is a *quasiperiod* of $chi_m$ if for any $a, b in ZZ$ such that $[a],[b] in (bb(Z) \/ m bb(Z))^times$ , we have
  $
    a equiv b med mod med q ==> chi_m (a) = chi_m (b).
  $
  The *conductor* #index("Dirichlet Character", "conductor") of $chi_m$ is defined as the smallest quasiperiod of $chi_m$.

]

#proposition[
  - If $q$ is the conductor of a Dirichlet character $chi_m$ modulo $m$, then $q | m$ and
    $
      & chi_m (a) = chi_q (a ) bold(1)_([a] in (bb(Z) \/ m bb(Z))^times)
    $
    for some Dirichlet character $chi_q$ modulo $q$.
  - The conductor of a Dirichlet character modulo $m$ is the smallest positive integer $q$ such that $chi_m$ can be induced by a Dirichlet character $chi_q$ modulo $q$.
  - A Dirichlet character modulo $m$ is primitive if and only if its conductor is $m$.
]


#example[Dirichlet Character of Modulus $1$][
  The unique Dirichlet character of modulus $1$ is the constant function
  $
    chi_1 (a) = 1.
  $
  A principal Dirichlet character is primitive if and only if its modulus is $1$.
]

#definition[Parity of Dirichlet Character][
  Let $chi_m$ be a Dirichlet character modulo $m$. We say $chi_m$ is *even* if $chi_m (-1) = 1$ and *odd* if $chi_m (-1) = -1$. #index("Dirichlet character", "parity")
]<parity-of-dirichlet-character>

#definition[Order of Dirichlet Character][
  Let $chi_m$ be a Dirichlet character modulo $m$. The #strong[order] of $chi_m$ is defined as the smallest positive integer $k$ such that $chi_m^k = chi_(m,1)$, which is exactly the order of $chi_m^star$ in $algdual(((ZZ\/m ZZ)^times))=op("Hom")_(sans("Ab"))((ZZ\/m ZZ)^times,CC^times)$. #index("Dirichlet character", "order")
]

#definition[Quadratic Dirichlet Character][
  A Dirichlet character $chi_m$ modulo $m$ is called a #strong[quadratic Dirichlet character] if the order of $chi_m$ is $2$. #index("Dirichlet character", "quadratic")
]
#proposition[Orthogonality of Dirichlet Character][
  - Let $chi_m$ be a Dirichlet characters modulo $m$. Then we have
  $
    sum_(k = 1)^(m) chi_m (k) = cases(
      phi(m) & upright(" if") chi_m = chi_(m,1),
      0 & upright(" if") chi_m eq.not chi_(m,1)
    )
  $
  - Given $n in ZZ$,
  $
    sum_(chi^star in algdual(((ZZ\/m ZZ)^times)) )chi (n) = cases(
      phi(m) & upright(" if") n equiv 1 mod m,
      0 & upright(" if") n equiv.not 1 mod m
    )
  $
]
#proof[
  This follows from @orthogonality-of-characters-of-finite-abelian-group.
]


#corollary[][
  Let $chi_m$ be a Dirichlet character modulo $m$. Suppose $n in ZZ$ and $[a] in (ZZ\/m ZZ)^times$. Then we have
  $
    1 / (phi(a)) sum_(chi^star in algdual(((ZZ\/m ZZ)^times)) )overline(chi)(a)chi (n) = cases(
      1 & upright(" if") n equiv a mod m,
      0 & upright(" if") n equiv.not a mod m
    )
  $
]


== Dirichlet $L$-Function

#definition[Dirichlet $L$-function][
  Given any Dirichlet character $chi: ZZ -> CC$, the #strong[Dirichlet
    $L$-series] is defined as #index_math(display: [$L(s, chi)$], "L(s, chi)")
  $
    L(s, chi) = sum_(n = 1)^oo chi(n) / n^(s)
  $
  which is absolutely convergent for $upright(R e)(s) > 1$. It can be extended to a meromorphic function on the whole complex plane, and is then called a *Dirichlet $L$-function*. #index(display: [$L$-function], "L-function") #index("L-function", "Dirichlet")
]

#proposition[Euler Product Formula for Dirichlet $L$-functions][
  For any Dirichlet character $chi: ZZ -> CC$, the Dirichlet L-function $L(s, chi)$ has the following properties:
  $
    L(s, chi) = product_(p "prime") 1 / (1 - chi (p) p^(-s)) " for " upright(R e)(s) > 1.
  $
]

#definition[Gauss Sum of Dirichlet Character][
  Let $chi$ be a Dirichlet character modulo $m$. The #strong[Gauss sum]#index("Gauss Sum") of $chi$ is defined as #index_math(display: [$G(chi)$], "G(chi)")
  $
    G(chi)=sum_(a = 1)^(m) chi(a) e^((2 pi i a) / m).
  $
]


#proposition[Properties of Gauss Sum][
  Let $chi$ be a Dirichlet character modulo $m$. The Gauss sum of $chi$ has the following properties:
  + If $chi$ is primitive, then $|G(chi)| = sqrt(m)$.
]




#definition[Root Number of Dirichlet Character][
  Let $chi$ be a primitive Dirichlet character modulo $m$. The #strong[root number] #index("Dirichlet Character", "Root Number") of $chi$ is defined as
  $
    epsilon(chi)=G(chi) / (i^delta sqrt(q))=cases(
      G(chi)/( sqrt(q)) & " if" chi "is even,",
      -i G(chi)/( sqrt(q)) & " if" chi "is odd."
    )
  $
  #index_math(display: [$epsilon(chi)$], "epsilon(chi)")
]

#proposition[Properties of Root Number][
  Let $chi$ be a primitive Dirichlet character modulo $m$. The root number of $chi$ has the following properties:

  + $|epsilon(chi)| = 1$.

  + If $chi$ is a quadratic Dirichlet character, then $epsilon(chi) in {1, -1}$.
]


#proposition[Functional Equation for Dirichlet L-functions][
  Let $chi$ be a primitive Dirichlet character modulo $q$ with $q>1$. Let
  $
    delta = cases(
      0 & " if" chi(-1) = 1 "i.e." chi "is even,",
      1 & " if" chi(-1) = -1 "i.e." chi "is odd."
    )
  $
  The Euler factor of the Riemann zeta function at a prime $p$ is given by #index_math(display: [$L_p (s, chi)$], "L_p(s, chi)")
  $
    L_p (s, chi)=1 / (1 - chi (p) p^(-s)).
  $
  The Euler factor of the Dirichlet L-function at infinity is given by #index_math(display: [$L_(oo)(s, chi)$], "L_(oo)(s, chi)")
  $
    L_(oo)(s, chi)=pi^(-(s+delta) / 2) Gamma((s+delta) / 2) = cases(
      pi^(-s / 2) Gamma(s / 2) & " if" chi "is even,",
      pi^(-(s+1) / 2) Gamma((s+1) / 2) & " if" chi "is odd."
    )
  $
  Let
  $
    Lambda(s, chi) = product_v L_v (s,chi)=L_(oo)(s, chi)product_(p "prime")L_p (s,chi)=pi^(-(s+delta) / 2) Gamma((s+delta) / 2) L(s, chi),
  $
  and
  $
    W(s,chi)=epsilon(chi)q^(1 / 2-s)=(G(chi)q^(-s)) / (i^delta)=cases(
      G(chi)q^(-s) & " if" chi "is even,",
      -i G(chi)q^(-s) & " if" chi "is odd."
    )
  $
  Then $Lambda(s, chi)$ satisfies the following functional equation
  $
    Lambda(s, chi)=W(s,chi)Lambda(1-s, overline(chi))=epsilon(chi) q^(1 / 2-s)Lambda(1-s, overline(chi)).
  $
]

#example[Dirichlet L-function of Primitive Dirichlet Character mod 4][
  There are 2 Dirichlet characters modulo $4$. Let $chi_4$ be the unique primitive Dirichlet character modulo $4$, which is defined by $chi_4 (3) = -1$. Then the Dirichlet $L$-series of $chi_4$ is given by
  $
    L(s, chi_4) & = 1 - 1 / 3^s + 1 / 5^s - 1 / 7^s + dots.c \
                & = sum_(n = 0)^oo (-1)^(n) / (2n + 1)^s \
                & = 1 / Gamma(s) integral_(0)^(oo) (x^(s - 1)e^(-x)) / (1+e^(-2x)) dif x.
  $
  It is absolutely convergent for $upright(R e)(s) > 0$ and can be extended to a meromorphic function on the whole complex plane. $L(s, chi_4)$ also called *Dirichlet beta function*#index("Dirichlet beta function").
  Its special values at odd positive integer are given by
  $
    L(2n + 1, chi_4) = ((-1)^n E_(2n)) / (2(2n)!)(pi / 2)^(2n+1) in pi^(2n+1) bb(Q),
  $
  where $E_(2n)$ is the $2n$-th Euler number. The number $L(2, chi_4)$ is known as *Catalan's constant*#index("Catalan's constant").

]

== Riemann Zeta Function

Riemann zeta function is a Dirichlet L-function associated to the principal Dirichlet character modulo $1$.

#definition[Riemann Zeta Function][
  The #strong[Riemann zeta function] is defined as #index_math(display: [$zeta(s)$], "zeta(s)")
  $
    zeta(s)=L(s,chi_1) = sum_(n = 1)^oo 1 / n^s
  $
  which is absolutely convergent for $upright(R e)(s) > 1$. It can be extended to a meromorphic function on the whole complex plane, and is then called a *Riemann zeta function*.
]
Thus the Riemann zeta function is a meromorphic function on the whole complex plane, which is holomorphic everywhere except for a simple pole at $s = 1$ with residue
$
  op("Res")_(s=1) zeta(s) = lim_(s -> 1) (s - 1) zeta(s) = 1.
$

The Euler factor of the Riemann zeta function at a prime $p$ is given by
$
  L_p (s, chi_1)=1 / (1 - p^(-s)).
$
The Euler factor of the Riemann zeta function at infinity is given by
$
  L_(oo)(s, chi_1)=pi^(-s / 2) Gamma(s/2).
$


#proposition[Properties of Riemann Zeta Function][
  The Riemann zeta function $zeta(s)$ has the following properties:

  + Euler product formula #h(1fr)
    $
      zeta(s) = product_(p "prime") L_p (s,chi_1) =product_(p "prime") 1 / (1 - p^(-s)).
    $

  + Functional equation
    $
      Lambda(s) = Lambda(1-s)
    $
    where $Lambda(s)=product_(v) L_v (s,chi_1)= pi^(-s/2) Gamma(s/2) zeta(s)$.

]

#proposition[Special Values of Riemann Zeta Function][
  The Riemann zeta function $\zeta(s)$ has the following special values:

  + For any $n in ZZ_(>0)$, #h(1fr)
    $
      zeta(2n) = ((-1)^(n+1) B_(2n) ) / (2(2n)!)(2 pi)^(2n) in pi^(2n) bb(Q),
    $
    where $B_(2n)$ is the $2n$-th Bernoulli number.

  + For any $n in ZZ_(>=0)$, #h(1fr)
    $
      zeta(-n) = -B_(n+1) / (n+1) in bb(Q).
    $

  + $zeta(0) = -1 / 2$, $zeta(-1) = -1 / 12$, $zeta(- n) = 0$ for any $n in ZZ_(>0)$.
]

#definition[Jacobi Theta Function][
  The #strong[Jacobi theta function] is defined as
  $
    theta.alt (z ; tau) = sum_(n = -oo)^(oo) e^(pi i n^2 tau + 2 pi i n z),quad tau in HH, z in CC.
  $

]


#proposition[Jacobi Identity][
  The Jacobi theta function satisfies the following identity:
  $
    theta.alt (z ; tau) = 1/(- i tau)^(1/2) e^((pi i z^2)/tau) theta.alt (z / tau ; -1 / tau),quad tau in HH, z in CC.
  $
  Suppose $-i tau=r e^(i phi)$ where $phi in (-pi / 2, pi / 2)$. In the above formula, we choose the principal branch of the square root function, which is defined as
  $
    (-i tau)^(1/2) = r^(1/2) e^(i phi / 2).
  $
]


#corollary()[][
  Define
  $
    theta(t) = theta.alt (0 ; i t) = sum_(n = -oo)^(oo) e^(-pi n^2 t), quad t in (0, oo).
  $
  Then we have
  $
    theta(t) = 1/sqrt(t) thin theta(1/t)
  $
]
#proof[
  By setting $tau = i t$ and $z = 0$, we get
  $
    theta.alt (0 ; i t) =1/(- i i t)^(1/2) theta.alt (0 ; -1 / (i t)) =1/sqrt(t) theta.alt (0 ; i / t) = 1/sqrt(t) thin theta(1/t) .
  $

]

#pagebreak()

= Langlands Program For $bold(n=1)$ <langlands-program>

== Automorphic Side
#definition[Hecke Character][
  A #strong[Hecke character] #index("Hecke character") of $AA_QQ^times$ is a continuous group homomorphism
  $
    omega: QQ^times \\AA_QQ^times --> CC^times
  $
]
A Hecke character $omega$ is said to be *unitary* if
$
  omega(QQ^times \\AA_QQ^times) subset.eq U(1) = {z in CC^times : abs(z) = 1}.
$

The following lemma is handy as it provides an equivalent definition of a unitary Hecke character.
#lemma[][
  Let $pi.alt: AA_QQ^times -> CC^times$ be a function. Suppose $pi.alt$ satisfies the following properties:
  + For any $g_1, g_2 in AA_QQ^times$,
    $
      pi.alt(g_1 g_2) = pi.alt(g_1) pi.alt(g_2).
    $

  + For any $gamma in QQ^times$, $g in AA_QQ^times$,
    $
      pi.alt(gamma g) = pi.alt(g).
    $

  + $pi.alt$ is continuous at $1_AA_QQ^times=(1, 1, 1, dots.c)$.

  + For any $g in AA_QQ^times$, $|pi.alt(g)|=1$.

  By the universal property of quotient group, there exists a unique group homomorphism $omega:QQ^times \\AA_QQ^times -> CC^times$ such that the following diagram commutes
  #commutative_diagram(
    $
                 AA_QQ^times edge("d", ->>, pi) edge(->, pi.alt) & CC^times \
      QQ^times \\AA_QQ^times edge("ru", "hook->", omega, #right)
    $,
  )
  Furthermore, $omega$ is a unitary Hecke character of $AA_QQ^times$.
]
#proof[
  From (i) and (iii), we see $rho$ is a continuous group homomorphism. From (ii), it is straightforward to deduce that
  $
    QQ^times subset.eq ker (rho),
  $
  which induces a unique continous group homomorphism $omega:QQ^times \\AA_QQ^times -> CC^times$ by the universal property of quotient topological group. The unitarity of $omega$ follows from (iv).
]

#proposition[Properties of Hecke Character][
  Let $pi.alt: AA_QQ^times -> CC^times$ be a unitary Hecke character. Then we have

  + For any $gamma in QQ^times$, $pi.alt(gamma) = 1$.
]

#proof[
  + Given any $gamma in QQ^times$, we have
    $
      pi.alt(gamma) =pi.alt(gamma dot 1_(AA_QQ^times))=pi.alt(1_(AA_QQ^times))=1.
    $
]

#definition[Local Hecke Character][
  Let $pi.alt: AA_QQ^times -> CC^times$ be a Hecke character and $v$ be a place of $QQ$. A #strong[local Hecke character] at $v$ is a continuous group homomorphism defined as
  $
    pi.alt_v:= pi.alt compose i_v: QQ_v & --> CC^times \
                                    g_v & mapsto.long pi.alt(i_v (g_v))= pi.alt(1, dots.c, 1, g_v, 1, dots.c)
  $
]


#definition[Unramified Local Hecke Character][
  Let $pi.alt: AA_QQ^times -> CC^times$ be a Hecke character and $v$ be a place of $QQ$. Let $pi.alt_v:= pi.alt compose i_v: QQ_v$ be the local Hecke character at $v$. We say $pi.alt_v$ is #strong[unramified] if

  + $v=p$ is a prime place of $QQ$: $pi.alt_p$ is trivial on $ZZ_p^times$, that  is, for any $g_p in ZZ_p^times$, $pi.alt_p (g_p) = 1$.

  + $v=oo$ is the infinite place of $QQ$: $pi.alt_oo (g_oo)= abs(g_oo)^(i t)$.

]

#proposition[Properties of  Hecke Character][
  Let $pi.alt: AA_QQ^times -> CC^times$ be a local Hecke character and $v$ be a place of $QQ$. Then we have

  + For any $gamma in QQ^times$ and any $g_v in QQ_v$, $pi.alt_v (gamma g_v) = pi.alt_v (g_v)$.
  + For any $g_v in QQ_v$, $|pi.alt_v (g_v)| = 1$.

]

#proposition[Properties of Local Hecke Character][
  Let $pi.alt: AA_QQ^times -> CC^times$ be a local Hecke character and $v$ be a place of $QQ$. If $pi.alt_v$ is unramified at a prime place $p$, then we have
  + For any $g_p in QQ_p^times$,
    $
      pi.alt_p (g_p) = pi.alt_p (p)^(v_p (g_p)).
    $
    So once we know the value of $pi.alt_p (p)$, we can determine the value of $pi.alt_p (g_p)$ for any $g_p in QQ_p^times$.
]

#definition[Moderate Growth][
  We say that a function $phi.alt: AA_QQ^times -> CC$ is of #strong[moderate growth] if for any $g=(g_oo, g_2,g_3, dots.c) in AA_QQ^times$, there exist constant $C_g > 0$ and $M_g>0$ such that
  $
    abs(phi.alt(t g_oo, g_2, g_3, dots.c)) <= C_g (1+abs(t))^(M_g), quad forall t in RR.
  $
]

#definition[Automorphic Form for $GL_1(AA_QQ)$][
  Let $pi.alt: AA_QQ^times -> CC^times$ be a unitary Hecke character of $AA_QQ^times$. A #strong[automorphic form] for $GL_1(AA_QQ)$ with character $pi.alt$ is a function $phi.alt: AA_QQ^times -> CC$ such that

  + For any $gamma in QQ^times$ and $g in AA_QQ^times$,
    $
      phi.alt(gamma g) = phi.alt(g).
    $

  + For any $z in AA_QQ^times$ and $g in AA_QQ^times$,
    $
      phi.alt(z g) = pi.alt(z) phi.alt(g).
    $
  + $phi.alt$ is of moderate growth.
]<automorphic-form-for-gl_1>
#let autoformspace(x) = $A_(#x)$
#example[Linear Space of Automorphic Forms][
  Let $pi.alt: AA_QQ^times -> CC^times$ be a unitary Hecke character of $AA_QQ^times$. The #strong[linear space of automorphic forms] for $GL_1(AA_QQ)$ with character $pi.alt$ is defined as
  $
    autoformspace(pi.alt) = {phi.alt: AA_QQ^times -> CC | phi.alt "is an automorphic form for" GL_1(AA_QQ) "with character" pi.alt},
  $
  Then we have
  $
    autoformspace(pi.alt) = {c pi.alt | c in CC}
  $
  and $dim autoformspace(pi.alt) = 1$.
]
#proof[
  Given any $phi.alt_1, phi.alt_2 in autoformspace(pi.alt)$ and $lambda in CC$, we have
  + For any $gamma in QQ^times$ and $g in AA_QQ^times$,
    $
      (phi.alt_1 + lambda phi.alt_2)(gamma g) = phi.alt_1(gamma g) + lambda phi.alt_2(gamma g) = phi.alt_1(g) + lambda phi.alt_2(g) = (phi.alt_1 + lambda phi.alt_2)(g).
    $

  + For any $z in AA_QQ^times$ and $g in AA_QQ^times$,
  $
    (phi.alt_1 + lambda phi.alt_2)(z g) = phi.alt_1(z g) + lambda phi.alt_2(z g) = pi.alt(z) phi.alt_1(g) + lambda pi.alt(z) phi.alt_2(g) = pi.alt(z)(phi.alt_1 + lambda phi.alt_2)(g).
  $

  + For any $g=(g_oo, g_2, g_3, dots.c) in AA_QQ^times$, there exist constant $C_g > 0$ and $M_g>0$ such that
    $
      abs(phi.alt_1 (t g_oo, g_2, g_3, dots.c)) <= C_g (1+abs(t))^(M_g), quad forall t in RR.
    $
    and there exist constant $C'_g > 0$ and $M'_g>0$ such that
    $
      abs(phi.alt_2(t g_oo, g_2, g_3, dots.c)) <= C'_g (1+abs(t))^(M'_g), quad forall t in RR.
    $
    Therefore, we there exist constant $C''_g = C_g + |lambda| C'_g > 0$ and $M''_g = max(M_g, M'_g)$ such that
    $
      abs((phi.alt_1 + lambda phi.alt_2)(t g_oo, g_2, g_3, dots.c)) <= C_g (1+abs(t))^(M_g) + |lambda| C'_g (1+abs(t))^(M'_g) <= C''_g (1+abs(t))^(M''_g), quad forall t in RR,
    $
    which means $phi.alt_1 + lambda phi.alt_2$ is of moderate growth.

  Thus, $phi.alt_1 + lambda phi.alt_2$ is an automorphic form for $GL_1(AA_QQ)$ with character $pi.alt$. Therefore, $autoformspace(pi.alt)$ is a complex linear space.

  For any $z in AA_QQ^times$, if we take $g=1_(AA_QQ^times)$, then we have
  $
    phi.alt(z) =phi.alt(z dot 1_(AA_QQ^times))= pi.alt(z) phi.alt(1_(AA_QQ^times)) = pi.alt(z) phi.alt(1_(AA_QQ^times)),
  $
  which means $phi.alt$ is completely determined by its value at $1_(AA_QQ^times)$. Therefore, an automorphic form for $GL_1(AA_QQ)$ with character $pi.alt$ is just $pi.alt$ scaled by a complex number, which means $dim autoformspace(pi.alt)=1$.

]

#definition[Idelic Lift of a Dirichlet Character][
  Let $chi$ be a Dirichlet character of modulus $p^f$ where $p$ is a prime number and $f$ is a positive integer. The *idelic lift* of $chi$ is a unitary Hecke character $chi_("idelic"): AA_QQ^times -> CC^times$ defined as follows:
  $
    chi_("idelic")(g) = chi_oo (g_oo) product_(v < oo) chi_v (g_v), quad forall g=(g_oo, g_2, g_3,dots.c) in AA_QQ^times,
  $
  where
  $
    chi_oo (g_oo) & = cases(
                      -1\, & quad "if" chi "is odd, and" g_oo < 0,
                      1\, & quad upright("otherwise")
                    ) \
      chi_v (g_v) & = cases(
                      chi(v)^m \, & quad "if" v != p "and" g_v in v^m ZZ_v^times,
                      chi(j)^(-1) & quad "if" v = p "and" g_v in p^k (j+p^f ZZ_v) "with" j\,k in ZZ\, med gcd(j, p)=1
                    )
  $
  and $v$ is a prime number.
]<idelic-lift-of-a-dirichlet-character>
#remark[

]

#proposition[Pontryagin Dual of $RR^times$][
  Every unitary continuous multiplicative character $omega_oo: RR^times -> CC^times$ is of the form
  $
    omega_oo (g_oo) = abs(g_oo)^(i t), quad forall g_oo in RR^times
  $
  or
  $
    omega_oo (g_oo) = op("sgn")(g_oo) dot abs(g_oo)^(i t) , quad forall g_oo in RR^times
  $
  where $t in RR$ is a constant. And the Pontryagin dual of $RR^times$ is given by
  $
    algdual((RR^times)) = {op("sgn")(g_oo)^(epsilon) dot abs(g_oo)^(i t) mid(|) thin [epsilon] in ZZ\/2ZZ, med t in RR} tilde.equiv ZZ\/2ZZ times RR.
  $

]


#theorem[Structure of Space of Automorphic Forms on $GL_1(AA_QQ)$][
  Every #link(<automorphic-form-for-gl_1>)[automorphic form] $phi.alt$ on $GL_1 (bb(A)_(bb(Q)))$, can be uniquely expressed in the form
  $
    phi.alt: AA_QQ^times & --> CC \
                       g & mapsto.long c dot.op chi_(upright("idelic")) (g) dot.op abs(g)_(bb(A))^(i t),
  $
  where $c in bb(C) \, t in bb(R)$, are fixed constants, and
  $chi_(upright("idelic"))$ is an #link(<idelic-lift-of-a-dirichlet-character>)[idelic lift] of a fixed Dirichlet character $chi$. Here, if $g = (g_oo \, g_2 , g_3 , dots.c)$, then $abs(g)_(bb(A)) = product_(v ) abs(g_v)_v$ is the
  idelic absolute value.
]

=== $L$-function of Automorphic Form



== Motivic Side

=== Artin $L$-Function

#definition[Artin $L$-function][
  Let $K$ be a number field and $rho: Gal(overline(K)\/K) -> GL_n (CC)$ be a continuous representation of the absolute Galois group of $K$. The #strong[Artin $L$-function] #index("Artin L-function") associated to $rho$ is defined as
  $
    L(s, rho) = product_(v in mono("pl")_K) L_v (s, rho)
  $
  where $L_v (s, rho)$ is the local $L$-function associated to $rho$ at $v$, which is defined as
  $
    L_v (s, rho) = det(1 - rho(Frob_v) N(v)^(-s))^(-1).
  $
]

#definition[Artin $L$-function over $QQ$][
  Let $rho: Gal(overline(QQ)\/QQ) -> GL_n (CC)$ be a continuous representation of the absolute Galois group of $QQ$. The #strong[Artin $L$-function over $QQ$] #index("Artin L-function") associated to $rho$ is defined as
  $
    L(s, rho) = product_(p "prime") L_p (s, rho)
  $
  where $L_p (s, rho)$ is the local $L$-function associated to $rho$ at $p$, which is defined as
  $
    L_p (s, rho) = det(1 - rho(Frob_p) p^(-s))^(-1).
  $
]

#lemma[Compact Subgroup of $CC^times$][
  The only compact subgroups of $CC^times$ are:

  + The unit circle
  $
    TT= {z in CC^times mid(|) z = 1}.
  $

  + The groups of $n$-th roots of unity
  $
    mu_n= {z in CC^times mid(|) z^n = 1} tilde.equiv ZZ\/n ZZ.
  $

]

#proposition[][
  Let $K$ be a field. Every continuous homomorphism $rho: Gal(K^(op("sep"))\/K) -> CC^times$ factors through the Galois group of a finite cyclic extension $L\/K$, yielding the epimorphism-monomorphism decomposition
  #commutative_diagram(
    $
      Gal(K^(op("sep"))\/K) edge("d", ->>, pi) edge(->, rho) & CC^times \
                Gal(L\/K) edge("ru", "hook->", iota, #right)
    $,
  )
]
#proof[
  Denote $G_K=Gal(K^(op("sep"))\/K)$. Since $Gal(K^(op("sep"))\/K)$ is a profinite group, it is compact. Recall the fact that the image of a compact set under a continuous map is compact. Therefore, $rho(G_K)$ is a compact subgroup of $CC^times$. Since the only compact subgroups of $CC^times$ are
  groups of roots of unity, there exists $n in ZZ_(>0)$ such that
  $
    rho(G_K)=mu_n= {z in CC^times mid(|) z^n = 1} tilde.equiv ZZ\/n ZZ.
  $
]


