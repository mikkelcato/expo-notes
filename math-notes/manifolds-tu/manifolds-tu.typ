#import "@preview/physica:0.9.5": *
#import "temp.typ": *


#show: thmrules.with(qed-symbol: $square$)
#show: note.with(
  title: [
    *manifolds*
  ],
  authors: (
    (
      name: "mikkelius_",
    ),
  ),
  abstract: [
    notes on _An Introduction to Manifolds_ by L. W. Tu.
  ],
)

#pagebreak()
= Smooth Functions on a Euclidean Space
We'll write coordinates on $RR^n$ as $x^1,dots,x^n$ and let $p = (p^1,dots,p^n)$ be a point in an open set $U subset.eq RR^n$.

#def[$C^k$ and $C^oo$][A function $f:U arrow RR$ is $C^k$ at $p$ if all partial derivative of order $j <= k$ exists and are continuous as $p$. $f$ is $C^oo$ at $p$ if it is $C^k$ for all $k >= 0$. A function is $C^k$ on $U$ if it is $C^k$ at every point, similarly for $C^oo$ -- we call these functions smooth.]

#ex[
  - A $C^0$ function on $U$ is continuous on $U$.

  - Polynomial-, sine-, cosine-, and exponential functions on $RR$ are all $C^oo$
]

We say a function $f$ is real-analytic at $p$ if in some neighborhood of $p$ it is equal to its Taylor series at $p$. These are necessarily $C^oo$, since convergent power series are differentiable in their region of convergence -- the opposite is not true. (consider a function all of whose derivatives vanish at $0$ $arrow$ Taylor series would be identically $0$ in any neighborhood of the origin.)

#thm[Taylor's theorem with remainder][
  Let $f$ be $C^oo$ on an open subset $U subset.eq RR^n$ star-shaped with respect to $p = (p^1, dots, p^n) in U$. Then there are $C^oo$ $g_1 (x), dots, g_n (x)$ on $U$ such that: $ f(x)=f(p)+sum_(i=1)^n (x^i - p^i)g_i (x)",  " g_i (p) = pdv(f, x^i) (p) $
]
#proof[
  Basically differentiate $f(p+t(x-p))$ and the result follows by integration.
]

#ex[
  Let $U subset RR^n$ and $V subset RR^n$ be open. A $C^oo$ map $F: U arrow V$ is a diffeomorphism if it is bijective and has a $C^oo$ inverse $F^(-1): V arrow U$.

  - $f:(-pi/2,pi/2) arrow RR "with" f(x) = tan x$ is a diffeomorphism.
  - Want a linear function $h:(a,b)arrow (-1,1)$, proving that any two finite open intervals are diffeomorphic. We want $h(x) = alpha x +beta$, so $h(a)=-1 "and" h(b)=1$ this gives $h(x)=(2(x-a))/(b-a)-1$.
  - The composite $f compose h : (a,b) arrow RR$ is then a diffeomorphism of an open interval to $RR$.
]

#ex[
  Define $f:RR arrow RR$ by $f(x) = x^3$. $f$ is a bijective $C^oo$ map, since polynomial. But $f^(-1)$ is not, taking the derivative gives division by zero problems and thus singularities making it discontinuous.
]

#pagebreak()
= Tangent Vectors in $RR^n$ as Derivations
== Directional derivative
A vector at $p$ is tangent to a surface at $p$ if it lies in the tangent plane at $p$. We denote the tangent space at $p$ as $T_p (RR^n)$. It is common to just call the tangent vectors for vectors and denote them like normal vectors. The line through $p$ with direction $v$ in $RR^n$ has parametrization $ c(t)=(p^1+t v^1,dots,p^n + t v^n) = p + t v $ if $f$ is $C^oo$ in a neighborhood of $p$ in $RR^n$ and $v$ is the tangent vector at $p$, then we define the directional derivative of $f$ in the direction of $v$ at $p$ as
$
  D_v f &= lim_(t arrow 0) (f(c(t))-f(p))/t = evaluated(dv(, t))_(t=0) f(c(t)) \
  &= sum_(i=1)^n v^i pdv(f, x^i) (p) => D_v = sum v^i evaluated(pdv(, x^i))_p
$
note that this is a scalar, many times the $p$ is omitted. Note also that all vectors in $T_p (RR^n)$ are basically all vectors with the partial derivatives as the basis.

== Germs
If two functions agree on some neighborhood of $p$, then they'll have the same directional derivative at $p$. Consider all pairs $(f,U)$ where $U$ is a neighborhood of $p$ and $f:U arrow RR$ is $C^oo$. We say $(f,U)$ is equivalent to $(g,V)$ if there is some open set $W subset.eq U inter V$ with $p in W$ such that $f = g$ on $W$. This is an equivalence relation, since it is reflexive, symmetric and transitive. The equivalence class of $(f,U)$ is called the germ of $f$ at $p$. We write $C_p^oo (RR^n)$ as the set of all germs of $C^oo$ functions on $RR^n$ at $p$.

#ex[
  Consider $f(x)=(1-x)^(-1)$ with domain $RR \\ {1}$ and $g(x)=1+x+x^2+dots$ with domain $(-1,1)$. These have the same germ at any $p in (-1,1)$, since $g(x)$ converges to $f(x)$ for any such $p$.
]

So the germ is the equivalence class of all functions that agree with a given function near $p$.

#def[Algebra][
  An algebra over a field $K$ is a vector space $A$ over $K$ with a multiplication map $mu : A times A arrow A$, such that for all $a,b,c in A$ and $r in K$:
  - $(a times b) times c = a times (b times c)$
  - $(a+b)times c = a times c + b times c$ and $a times ( b + c) = a times b + a times c$
  - $r (a times b) = (r a) times b = a times (r b)$
  Equivalently an algebra over a field $K$ is a ring $A$ which is also a vector space, such that ring multiplication satisfies homogeneity.
]

== Derivations
#def[Linear map][
  A map $L : V arrow W$ between vector spaces over a field $K$ is a linear map or linear operator if for all $r in K$ and $u,v in V$:
  - $L(u+v)=L(u)+L(v)$
  - $L(r v)=r L (v)$
]
For any tangent vector $v$ at $p in RR^n$ we have $ D_v : C_p^oo arrow RR $ and it satisfies the Leibniz rule: $ D_v (f g) = (D_v f)g(p)+f(p) D_v g $ simply because the partial derivatives are nice. Any linear map $D:C_p^oo arrow RR$ satisfying this property is called a derivation at $p$. We denote all derivations at $p$ by $cal(D)_p (RR^n)$, which turns out be a vector space, i.e. closed under addition and scalar multiplication. All $D_v (p)$ are derivations at $p$ so we have a map $ phi : T_p (RR^n) & arrow cal(D)_p (RR^n) \
               v & |->D_v = sum v^i evaluated(pdv(, x^i))_p $ $D_v$ is clearly linear in $v$, so the map $phi$ is a linear operator of vector spaces.

#lemma[
  If $D$ is a derivation at $p$, then $D(c)=0$ for any constant function $c$.
]
#proof[
  By $RR$-linearity $D(c)=c D(1)$, so we need to show that $D(1)=0$. By the Leibniz rule: $ D(1)=D(1 times 1) = D(1)times 1 + 1 times D(1)=2 D(1) => D(1)=0 $
]

#thm[
  The linear map $phi: T_p (RR^n) arrow cal(D)_p (RR^n)$ is an isomorphism of vector spaces.
]
#proof[
  We have to show bijectivity. For injectivity ($phi(v)=0 <=> v = 0$) suppose $D_v = 0$ for $v in T_p (RR^n)$. Then applying $D_v$ to the coordinate function $x^j$ gives: $ 0 = D_v (x^j) = sum_i v^i evaluated(pdv(, x^i))_p x^j = sum_i v^i delta_i^j = v^j $ so $v=0$ and $phi$ is injective.

  For surjectivity let $D$ be a derivation at $p$ and let $(f,V)$ be a germ in $C_p^oo$, we want to show that there is some vector $v in T_p (RR^n)$ such that $D = D_v$. We'll assume $V$ is an open ball (star-shaped). By Taylor's theorem there are smooth functions $g_i (x)$ in a neighborhood of $p$ such that: $ f(x)=f(p)+sum (x^i - p^i) g_i (x)",  " g_i (p) = pdv(f, x^i) (p) $ applying $D$ to both sides and using $D(f(p))=0$ and $D(p^i)=0$ by previous lemma, then:
  $
    D f(x) & = sum (D x^i) g_i (p) + sum (p^i - p^i) D g_i (x) \
           & = sum (D x^i) pdv(f, x^i) (p)
  $
  so $D = D_v$ for $v = vecrow(D x^1, dots, D x^n) in T_p (RR^n)$ by construction.
]

So we have $T_p (RR^n) tilde.equiv cal(D)_p (RR^n)$, and we may identify the tangent vectors at $p$ with the derivations at $p$. Under this the standard basis ${e_1,dots,e_n}$ for $T_p (RR^n)$ corresponds to ${pdv(, x^1),dots,pdv(, x^n)}$ (all evaluated at $p$). Thus we'll write all tangent vectors as $ v=sum v^i evaluated(pdv(, x^i))_p $ with each vector corresponding to a derivation $D_v$ in $cal(D)_p (RR^n)$, and each derivation $D$ corresponding to a vector $v=(D x^i)$.

== Vector fields

