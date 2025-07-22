#import "@preview/physica:0.9.5": *
#import "temp.typ": *


#show: thmrules.with(qed-symbol: $square$)
#show: note.with(
  title: [
    *complex analysis*
  ],
  authors: (
    (
      name: "mikkelius_",
    ),
  ),
  abstract: [
    notes on _Complex Analysis_ by Ahlfors -- skipping some parts.
  ],
)


//****

= Complex functions
\* chpt. 2
== Analytic functions
_$z$ and $w$ will always denote complex variables, $x$ and $y$ can be either complex or real, but $t$ will be restricted to real values._

=== Limits and continuity
The usual limit and continuity definitions from real analysis are obvious. However there are some fundamental differences -- let $f(z)$ be a real function of a complex variable whose derivative exists at $z=a$, then $f'(a)$ is real as it is the limit of $ (f(a+h)-f(a))/h $ as $h arrow 0$ through real values, but it is also the limit of $ (f(a+i h) - f(a))/(i h) $ and thus imaginary. So $f'(a) =^! 0$ if the derivative exists. Similar logic applies to complex functions of a real variable $ z(t)=x(t)+i y(t) => z'(t)=x'(t)+i y'(t) $ so $z'(t)$ exists if both $x'(t)$ and $y'(t)$ exists.

=== Analyticity
Analytic (_Holomorphic_) functions are essentially complex functions of a complex variable with a derivative everywhere the function is defined -- these are very nice, and thus have nice properties i.e. products/quotients preserve analyticity.
From the definition we have
$
  f'(z) = lim_(h arrow 0) (f(z+h)-f(z))/h
$
note that this implies $f(z)$ is continuous, and if we let $f(z)=u(z)+i v(z)$ then it follows that both $u(z)$ and $v(z)$ are continuous. The limit must be the same regardless of how we let $h arrow 0$. Choosing real values for $h$ then the imaginary part of $z = x+ i y$ is constant, and the derivative becomes a partial derivative
$
  f'(z) = pdv(f, x) = pdv(u, x)+i pdv(v, x)
$
similarly for imaginary $h = i k$
$
  f'(z) = 1/i pdv(f, y) = - i pdv(u, y)+pdv(v, y)
$
thus $f(z)$ must satisfy
$
  pdv(f, x)=-i pdv(f, y)
$
this resolves to the Cauchy-Riemann equations:
#thm[Cauchy-Riemann equations][
  The Cauchy-Riemann equations are:
  $
    pdv(u, x)=pdv(v, y)",   " pdv(u, y)= - pdv(v, x)
  $
  These must be satisfied by the real and imaginary part of any analytic function $ f(z)=u(z)+i v(z) $
]
note that the partials exists if $f'(z)$ exists -- the relation goes both ways essentially, if $f'(z)$ exists, or $f(z)$ is analytic, then the CR-eq. are satisfied, and vice versa. To see why the derivatives exists consider
$
  abs(f'(z))^2 = (pdv(u, x))^2+(pdv(u, y))^2=(pdv(u, x))^2+(pdv(v, x))^2=pdv(u, x)pdv(v, y)-pdv(u, y)pdv(v, x)
$
where the last expression is just the Jacobian. Also note that we have
$
  nabla^2 u = pdv(u, x, 2)+pdv(u, y, 2)=0
$
and similarly for $v$, i.e. they satisfy the Laplace equation and are thus harmonic. (with $v$ being the conjugate harmonic function of $u$)

=== Polynomials and Rationals
All constant functions are analytic with derivative $0$, the simplest non-constant analytic function is $z$ whose derivative is $1$. It follows that every polynomial $ P(z) = a_0 + a_1 z + dots + a_n z^n $ is also analytic, with derivative
$
  P'(z) = a_1 + 2a_2 z + dots + n a_n z^(n-1)
$
we know that we can factorize any polynomial
$
  P(z) = a_n (z-alpha_1)(z-alpha_2) dots (z-alpha_n)
$
with $alpha_i$ being the roots of $P(z)$, these need not be distinct. If $h$ of the $alpha_j$ coincide we say this value of $alpha$ is a zero of $P(z)$ of order $h$. Thus the sum of all $h$ equal the order of the polynomial -- a degree $n$ polynomial has $n$ zeros. We can also consider derivatives. Letting $z = alpha$ be a zero of order $h$ then we can write $P(z)=(z-alpha)^h P_h (z)$ with $P_h(alpha) eq.not 0$. Differentiating yields $P(alpha)=P'(alpha)=dots=P^((h-1))(alpha)=0$, while $P^((h)) (alpha) eq.not 0$. So the order of a zero is the order of the first nonvanishing derivative. If $P(alpha)=0$ and $P'(alpha) eq.not 0$ then we call the zero simple. Now consider $ R(z) = P(z)/Q(z) $ we'll assume that $P(z)$ and $Q(z)$ have no common factors, and thus no common zeros. We'll give $R(z)$ the value $oo$ at the zeros of $Q(z)$, thus it is a function with values in the extended plane, and thus continuous. These zeros are usually called poles of $R(z)$, and the order of the pole is the order of the corresponding zero of $Q(z)$. Note that $R'(z)$ has the same poles, but with the order of each being increased by one. [_see pg. 30 in Ahlfors for more_]
Noteworthy is the fact that any $R(z)$ of order $p$ has $p$ zeros and $p$ poles, and every $R(z)=a$ has $p$ roots.

#pagebreak()
== Power series
Sequences and series (partial sums) are defined as usual -- note the Cauchy-criterion. Likewise pointwise and uniform convergence are defined as usual.

_Recall uniform convergence: The sequence ${f_n (x)}$ converges uniformly to $f(x)$ on the set $E$ if for every $epsilon > 0$ there exists an $n_0$ such that $abs(f_n (x)-f(x)) < epsilon$ for all $n >= n_0$ and for all $x in E$._

Uniform convergence is nice because continuity etc. is "preserved".

_Recall the Cauchy-criterion: ${f_n (x)}$ converges uniformly on $E$, if and only if for every $epsilon > 0$ there exists an $n_0$ such that $abs(f_m (x)- f_n (x)) < epsilon$ for all $m,n >= n_0$ and all $x in E$._

Now we can begin with power series of the form:
$
  a_0 + a_1 z + a_2 z^2 + dots + a_n z^n + dots
$
or more generally:
$
  sum_(n=0)^oo a_n (z-z_0)^n
$
the simplest example is the geometric series:
$
  1 + z +z^2+dots +z^n + dots
$
whose partial sums can be written in the form:
$
  1 + z + dots + z^(n-1) = (1-z^n)/(1-z)
$
since $z^n arrow 0$ for $abs(z)<1$ and $abs(z^n)>=1$ for $abs(z) >= 1$ it is clear that the series converges to $1\/(1-z)$ for $abs(z)<1$ and diverges for $abs(z)>=1$ -- this is very typical, i.e. convergence inside a circle and divergence outside it. To make this more concrete we have the following theorem:
#thm[Abel's theorem][
  For every power series there is a number $0 <= R <= oo$ called the radius of convergence, with the following properties:
  1. The series converges absoulutely for all $z$ with $abs(z)<R$. If $0 <= rho < R$ the convergence is uniform for $abs(z) <= rho$.
  2. If $abs(z) > R$ the terms of the series are unbounded, and the series is thus divergent.
  3. In $abs(z) < R$ the sum of the series is an analytic function. The derivative can be found by termwise differentiation and has the same radius of convergence.
]
We'll show the properties are true if $R$ is chosen as (_Hadamard's formula_):
$ 1/R = lim_(n arrow oo) sup root(n, abs(a_n)) $

#proof[
  If $abs(z) < R$ we can find $rho$ such that $abs(z) < rho < R$. Then $1\/rho > 1\/R$ and by definition of the $lim sup$ there exists an $n_0$ such that for all $n >= n_0$ we have $root(n, abs(a_n)) < 1\/rho => abs(a_n) < 1\/ rho^n$. It follows that $abs(a_n z^n) < (abs(z)\/rho)^n$ for large $n$, and thus the power series converges, since $abs(z)< rho$.

  To prove uniform convergence for $abs(z)<= rho < R$ we pick $rho'$ such that $rho < rho' < R$ and find $abs(a_n z^n) <= (rho \/rho')^n$ for $n >= n_0$. Again the majorant is convergent and since it has constant terms we use Weierstrass' M-test to conclude uniform convergence.

  If $abs(z) > R$ we pick $rho$ such that $R < rho < abs(z)$, since $1\/rho < 1\/R$ there are large $n$ such that $root(n, abs(a_n)) > 1\/rho => abs(a_n) > 1\/rho^n$. Thus $abs(a_n z^n) > (abs(z)\/rho)^n$ for infinitely many $n$, and the terms are unbounded.

  The derived series $sum_1^oo n a_n z^(n-1)$ has the same $R$ because $root(n, n) arrow 1$. To prove this we let $root(n, n) = 1 + delta_n$. Then $delta_n > 0$ and by the binomial theorem $n = (1+ delta_n)^n > 1 + 1/2 n(n-1) delta_n^2$ or $2\/n > delta_n^2$ and thus $delta_n arrow 0$.

  For $abs(z) < R$ we write:
  $ f(z) = sum_0^oo a_n z^n = s_n (z) + R_n (z) = sum_0^(n-1) a_k z^k + sum_(k=n)^oo a_k z^k $ and $ f_1 (z) = sum_1^oo n a_n z^(n-1) = lim_(n arrow oo) s'_n (z) $ we want to show that $f'(z)=f_1 (z)$. Consider:
  $
    (f(z)-f(z_0))/(z-z_0) - f_1 (z_0) = ((s_n (z)-s_n (z_0))/(z-z_0) - s'_n (z_0)) &+ (s'_n (z_0) - f_1 (z_0)) \
    &+ ((R_n (z) - R_n (z_0))/(z-z_0))
  $
  with $z eq.not z_0$ and $abs(z), abs(z_0) < rho < R$. The last term can be written as:
  $
    sum_(k=n)^oo a_k (z^(k-1) + z^(k-2)z_0 + dots + z z_0^(k-2) + z_0^(k-1))
  $
  which lets us say:
  $
    abs((R_n (z)-R_n (z_0))/(z-z_0)) <= sum_(k=n)^oo k abs(a_k) rho^(k-1)
  $
  the RHS is just the remainder term in a convergent series, thus we can find $n_0$ such that for all $n>=n_0$:
  $
    abs((R_n (z)-R_n (z_0))/(z-z_0)) <=epsilon/3
  $
  By definition we also have an $n_1$ such that for all $n >= n_1$: $abs(s'_n (z_0) - f_1 (z_0)) < epsilon\/3$. Pick $n >= n_0, n_1$, also by definition of the derivative we can find $delta > 0$ such that $0 < abs(z-z_0) < delta$ implies:
  $
    abs((s_n (z)- s_n (z_0))/(z-z_0)- s'_n (z_0)) < epsilon/3
  $
  combining everything we find:
  $
    abs((f(z)-f(z_0))/(z-z_0)-f_1 (z_0)) < epsilon
  $
  when $0 < abs(z-z_0) < delta$, thus $f'(z_0)$ exists and is equal to $f_1 (z_0)$.
]
This reasoning can be repeated, leading us to conclude that a power series with positive radius of convergence has derivatives of all orders, the $k$'th derivative is given as:
$
  f^((k)) (z) = k! a_k + ((k+1)!)/1! a_(k+1) z + ((k+2)!)/2! a_(k+2) z^2 + dots
$
giving $a_k = f^((k))(0) \/k!$, thus we can write our power series as:
$
  f(z) = f(0) + f'(0) z + (f''(0))/2! z^2 + dots + (f^((n))(0))/n! z^n + dots
$
which is just the Taylor-Maclaurin development.

=== The exponential and trigonometric functions
We define $e^x$ as the solution to $f'(z) = f(z)$ with initial value $f(0)=1$. This gives:
$
  e^z = 1 + z/1! + z^2/2! + dots + z^n/n! + dots
$
this series converges in the entire plane since $root(n, n!) arrow oo$.

We define the trigonometric functions by:
$
  cos z = (e^(i z) + e^(- i z))/2",   " sin z = (e^(i z)-e^(-i z))/(2i)
$
their series developments are obvious. From these definitions we also get Euler's formula:
$
  e^(i z) = cos z + i sin z
$
and:
$
  cos^2 z + sin^2 z = 1
$
likewise the usual derivatives follow, i.e. $dd(cos z) = - sin z$ and $dd(sin z) = cos z$ -- all other usual identities similarly follow from these definitions. Notably all trigonometric functions are rational functions of $e^(i z)$.

Functions are periodic with period $c$ if $f(z+c)=f(z)$, thus for the exponential $e^z e^c = e^z$ or $e^c = 1$. This implies $c = i omega$ with real $omega$. The smallest positive period is with $omega = 2 pi$. Further $e^(pi i \/2) = i$ and $e^(pi i) = -1$. Thus $w = e^(i y)$ describes the unit circle with $abs(w) = 1$ -- i.e. this is a homomorphism between the additive group of reals and the multiplicative group of complex numbers with absolute value $1$, with the kernel being all integral multiples $2pi n$.

We define the logarithm as the inverse of the exponential function, so by definition $z = log w$ is a root of $e^z = w$. Since $e^z eq.not 0$ the number $0$ has no logarithm. For $w eq.not 0$ then $e^(x+i y) = w$ implies $e^x = abs(w)$ and $e^(i y) = w \/ abs(w)$. The first equation has a unique solution $x = log abs(w)$ while the RHS of the second equation is a complex number of magnitude $1$, thus it has one solution in $0 <= y < 2 pi$, and is also satisfied by all $y$ that differ by an integer multiple of $2 pi$. So every complex number $eq.not 0$ has infinitely many logarithms which differ by multiples of $2 pi i$. The imaginary part of $log w$ is the argument of $w$ and is geometrically interpreted as the angle. With this definition $ log w = log abs(w) + i arg w $
or with $abs(z) = r$ and $arg z = theta$ then $z = r e^(i theta)$.

Lastly we'll find the inverse cosine. This is obtained by solving:
$
  cos z = (e^(i z) + e^(- i z))/2 = w
$
this can be written as a quadratic in $e^(i z)$ which gives the roots as:
$
  e^(i z) = w plus.minus sqrt(w^2 - 1) => z = arccos w = - i log(w plus.minus sqrt(w^2 -1))= plus.minus i log(w + sqrt(w^2-1))
$
the inverse sine is then easily defined by $ arcsin w = pi/2 - arccos w $
notably everything can be expressed in terms of $e^z$ and its inverse. Thus there is essentially only one elementary transcendental function.

#pagebreak()
= Complex integration
== Line integrals
\* chpt. 4

If $f(t) = u(t) + i v(t)$ is continuous and defined on $(a,b)$ then:
$
  integral_a^b f(t) dd(t) = integral_a^b u(t) dd(t) + i integral_a^b v(t) dd(t)
$
to generalize we use a line integral, consider a piecewise differentiable arc $gamma$ with $z = z(t)$ for $a <= t <= b$. Then given $f(z)$ is defined and continuous on $gamma$ then we can set:
$
  integral_gamma f(z) dd(z) = integral_a^b f(z(t)) z'(t) dd(t)
$
this is the complex line integral of $f(z)$ over $gamma$. Note that this integral is invariant under change of parameter, i.e. if $t = t(tau)$ is a change of parameter. Then:
$
  integral_a^b f(z(t))z'(t) dd(t) = integral_alpha^beta f(z(t(tau)))z'(t(tau))t'(tau) dd(tau)
$
but $z'(t) = z'(t(tau))t'(tau)$ so our integral is independent of how we parameterize $gamma$ which should hold. We define the opposite arc $-gamma$ by $z = z(-t)$ for $-b <= t <= - a$, thus:
$
  integral_(- gamma) f(z) dd(z) = integral_(-b)^(-a) f(z(-t))(-z'(-t))dd(t) = - integral_gamma f(z) dd(z)
$
if we subdivide our $gamma = gamma_1 + gamma_2 + dots + gamma_n$ then obviously:
$
  integral_gamma f dd(z) = integral_(gamma_1) f dd(z) + dots + integral_(gamma_n) f dd(z)
$
we can define:
$
  integral_gamma f overline(dd(z)) = overline(integral_gamma overline(f) dd(z))
$
and using this:
$
  integral_gamma f dd(x) = 1/2 { integral_gamma f dd(z) + integral_gamma f overline(dd(z)) }
$
similarly for the integral with respect to $y$. We could've also defined the integral as:
$
  integral_gamma (u dd(x) - v dd(y)) + i integral_gamma (u dd(y) + v dd(x))
$
which seperates the real and imaginary parts. An entirely different line integral can be obtained by integrating with respect to the arc length:
$
  integral_gamma f dd(s) = integral_gamma f abs(dd(z)) = integral_gamma f(z(t)) abs(z'(t)) dd(t)
$
this is also independent of choice of parameter, but now:
$
  integral_(- gamma) f abs(dd(z)) = integral_gamma f abs(dd(z))
$
note that for $f=1$ this integral just gives the length of $gamma$. The length can also be defined as the following limit:
$
  integral_gamma f dd(s) = lim sum_(k=1)^n f(z(t_k)) abs(z(t_k)-z(t_(k-1)))
$
if this is finite (with $f=1$) the arc is rectifiable, i.e. if we can find the length by splitting it up into small pieces, and finding the length of each piece.

A general line integral can be written in the form:
$
  integral_gamma p dd(x) + q dd(y)
$
often we treat this integral as dependent on $gamma$, thus as a functional. One type of such integrals are characterized by only depending on the end points of the arc. If two arcs have the same initial point and end point then we require:
$
  integral_(gamma_1) = integral_(gamma_2)
$
if $gamma$ is closed then $-gamma$ shares its end points thus we obtain:
$
  integral_gamma = integral_(- gamma) = - integral_gamma = 0
$
likewise if $gamma_1$ and $gamma_2$ share end points then $gamma_1 - gamma_2$ is a closed curve, and it follows that $ integral_(gamma_1) = integral_(gamma_2) $
but when does a line integral only depend on the end points?

#thm[
  The line integral $integral_gamma p dd(x)+q dd(y)$ in $Omega$ depends only on the end points of $gamma$ if and only if there is a function $U(x,y)$ in $Omega$ with partial derivatives $partial_x U = p$ and $partial_y U = q$.
]
#proof[
  Consider:
  $
    integral_gamma p dd(x) + q dd(y) = integral_a^b (pdv(U, x)x'(t) + pdv(U, y) y'(t))dd(t)=integral_a^b dv(U(x(t),y(t)), t) dd(t) = U(a)-U(b)
  $
  thus the integral only depends on the end points. To prove the other direction choose a point $(x_0, y_0) in Omega$ and join it to $(x,y)$ by a polygon $gamma$, contained in $Omega$, whose sides are parallel to the coordinate axes. And define a function $ U(x,y) = integral_gamma p dd(x) + q dd(y) $ This obviously only depends on the end points, so it is well-defined. If we now pick the last segment of $gamma$ horizontal, then we can keep $y$ constant and let $x$ vary without changing the other segments. So on the last segment we can write:
  $
    U (x,y) = integral^x p(x,y) dd(x) + "const"
  $
  where it immediately follows that $partial_x U = p$. If we let the last segment be vertical we'd get $partial_y U = q$. In other words we have:
  $
    dd(U) = pdv(U, x) dd(x) + pdv(U, y) dd(y)
  $
  or the integrand is an exact differential.
]
So when is $f(z) dd(z) = f(z) dd(x) + i f(z) dd(y)$ an exact differential? By definition for this to be the case we must have some $F(z)$ in $Omega$ with:
$
  pdv(F(z), x) & = f(z) \
  pdv(F(z), y) & = i f(z) \
               & => pdv(F, x) = - i pdv(F, y)
$
which is the CR-eq! Thus the integral $integral_gamma f dd(z)$, with continuous $f$ depends only on the end points of $gamma$ if and only if $f$ is the derivative of an analytic function in $Omega$. ($f$ itself is then also analytic.)

This is very powerful and lets us calculate some integrals without thinking.

#ex[
  $ integral_gamma (z-a)^n dd(z) = 0 $ for all closed $gamma$ if $n >= 0$. For negative $n eq.not 1$ the same holds for all closed curves which do not pass through $a$. For $n = -1$ this isn't true, consider a circle with center $a$: $z=a+rho e^(i t)$ for $0 <= t <= 2 pi$, doing the integral we obtain:
  $
    integral_C dd(z)/(z-a) = integral_0^(2 pi) i dd(t) = 2 pi i
  $
]
#ex[
  $ integral_(abs(z)=2) dd(z)/(z^2-1) $ we parameterize $z=2 e^(i t) => z'(t) = 2i e^(i t)$ giving:
  $
    integral_0^(2 pi) (2i e^(i t) dd(t))/(4e^(2 i t)-1)
  $
  consider:
  $
    f(t) = (2 i e^(i t))/(4 e^(2 i t)-1) => f(t+pi) = (2 i e^(i (t + pi)))/(4 e^(2 i(t+pi))-1) = (-2i e^(i t))/(4e^(2 i t)-1) = - f(t)
  $
  thus we can write:
  $
    integral_0^(2pi) f(t) dd(t) = integral_0^pi f(t) dd(t)+integral_pi^(2 pi) f(t) dd(t)
  $
  letting $t arrow t+pi$ in the first:
  $
    integral_pi^(2 pi) f(t+pi) dd(t) +integral_pi^(2 pi) f(t) dd(t) = 0
  $
  by the previous. Even though we have poles at $plus.minus 1$ the integral is zero due to symmetry.
]

#ex[
  $ integral_(abs(z)=1) abs(z-1) abs(dd(z)) $ we let $z = e^(i t) => dd(z) = i e^(i t) dd(t)$:
  $
    integral_0^(2 pi) abs(e^(i t) -1) dd(t)
  $
  now:
  $
    abs(e^(i t)-1)^2 = abs(cos t - 1 + i sin t)^2 = cos^2 t - 2 cos t +1 + sin^2 t = 2(1-cos t)
  $
  so:
  $
    sqrt(2) integral_0^(2 pi) sqrt(1-cos t) dd(t) &= 2 integral_0^(2 pi) abs(sin (t/2)) dd(t) \
    &= 4 integral_0^pi sin theta dd(theta) \
    &= 8
  $
]

#pagebreak()
== Cauchy's Theorem
We'll start by looking at a rectangle $R$ defined by $a <= x <= b$ and $c <= y <= d$. Its perimeter is a simple closed curve consisting of four line segments whose direction we choose such that $R$ lies to the left of the directed segments. This curve is referred to as the boundary curve or contour of $R$, and we denote it by $dd(R, d: partial)$ -- note that $R$ is a closed point set, and thus not a region, in the theorem we consider a function which is analytic on $R$, i.e. it is defined and analytic in an open set containing $R$.

#thm["Cauchy's Theorem"][
  If the function $f(z)$ is analytic on $R$, then:
  $
    integral_(dd(R, d: partial)) f(z) dd(z) = 0
  $
]

#proof[due to Goursat][
  We denote:
  $
    eta (R) = integral_(dd(R, d: partial)) f(z) dd(z)
  $
  and we proceed by bijection, dividing our rectangle into four congruent rectangles $R^((1)), R^((2)), R^((3))", and" R^((4))$, giving:
  $
    eta(R) = eta(R^((1))) + eta(R^((2)))+ eta(R^((3))) + eta(R^((4)))
  $
  since the integrals over the common sides obviously cancel. It follows that at least one rectangle must satisfy: $ abs(eta(R^((k)))) >= 1/4 abs(eta(R)) $ we let this rectangle be $R_1$, this can be repeated ad infinitum giving a sequence of nested rectangles $R supset R_1 supset R_2 supset dots supset R_n supset dots$ with:
  $
    abs(eta(R_n)) >= 4^(-n)abs(eta(R))
  $
  these converge to some $z^* in R$, or $R_n$ will be contained in some neighborhood $abs(z-z^*) < delta$ for large enough $n$. We pick $delta$ small enough such that $f(z)$ is defined and analytic in $abs(z-z^*) < delta$. Then given $epsilon > 0$ we can also pick $delta$ such that:
  $
    abs((f(z)-f(z^*))/(z-z^*)-f'(z^*)) < epsilon
  $
  or
  $
    abs(f(z)-f(z^*)-(z-z^*)f'(z^*)) < epsilon abs(z-z^*)
  $
  for $abs(z-z^*) < delta$. We assume $delta$ satisfies everything mentioned and that $R_n$ is contained in $abs(z-z^*) < delta$. We make the observation:
  $
    integral_(dd(R_n, d: partial)) dd(z) = integral_(dd(R_n, d: partial)) z dd(z) = 0
  $
  these are just special cases of our theorem that we have already proved since these are derivatives of $z$ and $z^2\/2$ respectively. These let us write:
  $
    eta (R_n) &= integral_(dd(R_n, d: partial)) f(z) dd(z) \
    &= integral_(dd(R_n, d: partial)) f(z)-f(z^*)-(z-z^*)f'(z^*) dd(z) \
    abs(eta(R_n))&<=epsilon integral_(dd(R_n, d: partial)) abs(z-z^*) abs(dd(z))
  $
  now $abs(z-z^*)$ is at most the length of the diagonal $d_n$ of $R_n$. If $L_n$ is the perimeter of $R_n$, then the integral is $<= d_n L_n$. If these are corresponding to the quantities of $R$ then $d_n = 2^(-n) d$ and $L_n = 2^(-n) L$, thus we get:
  $
    abs(eta(R_n)) <= 4^(-n) d L epsilon => abs(eta (R)) <= d L epsilon
  $
  $epsilon$ is arbritrary so $eta(R) =^! 0$. And we are done.
]

We can do better by weakening our hypothesis:
#thm[
  Let $f(z)$ be analytic on the set $R'$ obtained from $R$ by removing a finite number of interier points $zeta_j$. If for all $j$:
  $
    lim_(z arrow zeta_j) (z-zeta_j) f(z) = 0
  $
  then:
  $
    integral_(dd(R, d: partial)) f(z) dd(z) = 0
  $
]

#proof[
  To prove this we consider just one exceptional point $zeta$, since $R$ can be subdivided till each smaller rectangle contains at most one such point. Now we divide our $R$ into nine smaller rectangles with $zeta$ being in the middle rectangle, we call this rectangle $R_0$. Now we apply the previous theorem to every rectangle but $R_0$ to get:
  $
    integral_(dd(R, d: partial)) f dd(z) = integral_(dd(R_0, d: partial)) f dd(z)
  $
  given $epsilon > 0$ we can choose $R_0$ small enough such that:
  $
    lim_(z arrow zeta) (z- zeta)f(z) = 0 => abs(f(z)) <= epsilon/abs(z-zeta)
  $
  on $dd(R_0, d: partial)$. Then we have:
  $
    abs(integral_(dd(R, d: partial)) f dd(z)) <= epsilon integral_(dd(R_0, d: partial)) abs(dd(z))/abs(z - zeta)
  $
  if we assume that $R_0$ is a square with center $zeta$ then:
  $
    integral_(dd(R_0, d: partial)) abs(dd(z))/abs(z-zeta) < 8 => abs(integral_(dd(R, d: partial)) f dd(z)) < 8 epsilon
  $
  with arbitrary $epsilon$ the result follows. The hypothesis is fulfilled if $f(z)$ is analytic and bounded on $R'$.
]

We've seen that the integral of an analytic function over a closed curve doesn't always vanish, e.g:
$
  integral_C dd(z)/(z-a) = 2 pi i
$
to make sure it vanishes we need to make assumptions with respect to the region $Omega$ on which $f(z)$ is analytic. In the following we assume that $Omega$ is an open disk $abs(z-z_0) < rho$, which we denote by $Delta$.

#thm[
  If $f(z)$ is analytic in an open disk $Delta$, then:
  $
    integral_gamma f(z) dd(z) = 0
  $
  for every closed curve $gamma$ in $Delta$.
]

#proof[
  We define $F(z) = integral_sigma f dd(z)$ with $sigma$ being the horizontal line segment from $(x_0, y_0) arrow (x, y_0)$ and the vertical segment from $(x, y_0) arrow (x,y)$, it is then obvious that $partial_y F = i f(z)$, if we flip the zig-zag then we get $partial_x F = f(z)$. Then $F(z)$ is analytic in $Delta$ with derivative $f(z)$ and $f(z) dd(z)$ is an exact differential. We essentially construct rectangles within $Delta$ and then apply the previous theorems. This holds for regions which are somewhat symmetric, namely rectangles, circles, ellipsis, half planes, etc. We need the region to contain the rectangle made from opposite vertices $z$ and $z_0$.
]

For the reason stated the weaked hypothesis is also all thats needed in this case:

#thm[
  Let $f(z)$ be analytic in $Delta'$ obtained by removing a finite number of $zeta_j$ from an open disk $Delta$. If $f(z)$ satisfies $lim_(z arrow zeta_j) (z-zeta_j) f(z) = 0$ for all $j$, then $ integral_gamma f(z) dd(z) = 0 $ for any closed curve $gamma$ in $Delta'$.
]

#proof[(sketch)][
  Essentially the same proof, but we can't let $sigma$ pass through the points $zeta_j$. It is always possible to avoid these by using more lines.
]

#pagebreak()
== Cauchy's Integral Formula
As a preliminary we need to define the index of a point with respect to a closed curve. This is based on the following lemma:

#lemma[
  If the piecewise differentiable closed curve $gamma$ does not pass through the point $a$ then the value of the integral:
  $
    integral_gamma dd(z)/(z-a)
  $
  is a multiple of $2 pi i$.
]

#proof[
  One simple way to prove this is to just compute it. Let $gamma$ be parametrized by $z = z(t)$ for $alpha <= t <= beta$ and consider:
  $
    h(t) = integral_alpha^t (z'(t))/(z(t)-a) dd(t) => h'(t) = (z'(t))/(z(t)-a)
  $
  this is continuous and defined on $[alpha, beta]$ when $z'(t)$ is continuous. Now consider:
  $
    dv(, t) e^(- h(t)) (z(t)-a) = z'(t) e^(-h(t)) - (z(t)-a)e^(- h(t)) h'(t) = 0
  $
  except for points where $z(t)=a$. Thus this function must be constant, so we have, from $e^(-h(t)) (z(t)-a) = "const"$:
  $
    e^(h(t)) = (z(t)-a)/(z(alpha)-a)
  $
  given that $z(beta) = z(alpha)$ we get $e^(h(beta)) = 1$ so $h(beta)$ must be a multiple of $2 pi i$.
]
Now we can define the index (or winding number) as:
$
  n(gamma, a) = 1/(2 pi i) integral_gamma dd(z)/(z-a)
$
evidently $n(-gamma, a) = - n(gamma, a)$. Obviously if $gamma$ lies in a circle then $n(gamma, a) = 0$ for all points $a$ outside the same circle -- this is a consequence of Cauchy's theorem. Note that $gamma$ is closed and bounded, meaning its complement is open and can be represented as a union of disjoint regions. In a nutshell $gamma$ determines these regions. Considering the extended plane exactly one of these would hold the point at infinity. So $gamma$ determines one and only one unbounded region. The index $n(gamma, a)$ as a function of $a$ is constant in each region determined by $gamma$ and zero in the unbounded region. So for any two points $a$ and $b$ in the same region determined by $gamma$ have the same index, i.e. $n(gamma, a)=n(gamma, b)$. The case $n(gamma, a)=1$ is important, for simplicity we have the following lemma with $a=0$:

#lemma[
  Let $z_1, z_2$ be two points on a closed curve $gamma$, which does not pass through the origin. Denote the subarc from $z_1 arrow z_2$ by $gamma_1$ and the subarc from $z_2 arrow z_1$ by $gamma_2$. Assume that $z_1$ lies in the lower half plane, and $z_2$ in the upper half plane. If $gamma_1$ does not meet the negative real axis and $gamma_2$ does not meet the positive real axis, then $n(gamma, 0) = 1$.
]

#proof[
  The idea is to draw half-lines $L_1$ and $L_2$ from respectively $z_1$ and $z_2$ to the origin. Let $zeta_1$ and $zeta_2$ be points where $L_1$ and $L_2$ intersect a circle $C$ around the origin. The arc $C_1$ from $zeta_1 arrow zeta_2$ does not intersect the negative axis, and likewise $C_2$ does not intersect the positive axis. Denote the segments $z_1 arrow zeta_1$ by $delta_1$ and similarly for $delta_2$. Now we introduce the curves $sigma_1 = gamma_1 + delta_2 - C_1 - delta_1$ and $sigma_2 = gamma_2 + delta_1 - C_2 - delta_2$, both being closed. From these we can find:
  $
    gamma = gamma_1 + gamma_2 = sigma_1 + sigma_2 + C => n(gamma, 0) = n(sigma_1, 0) + n(sigma_2, 0) + n(C,0)
  $
  $sigma_1$ does not meet the negative axis, so the origin belongs to the unbounded region determined by $sigma_1$, and thus $n(sigma_1 , 0) = 0$, similarly $n(sigma_2, 0)=0$. So $n(gamma,0)=n(C,0)=1$.
]

Now let $f(z)$ be analytic in an open disk $Delta$. Consider a closed $gamma$ in $Delta$ and a point $a in Delta$ not on $gamma$. We'll apply Cauchy's theorem to:
$
  F(z) = (f(z)-f(a))/(z-a)
$
this function is analytic for all $z eq.not a$. For $z=a$ it is not defined, however it still satisfies $lim_(z arrow a) F(z)(z-a) = lim_(z arrow a) (f(z)-f(a))=0$, so the theorem still applies. Thus:
$
  integral_gamma (f(z)-f(a))/(z-a) dd(z) = 0
$
which can be written as:
$
  integral_gamma (f(z) dd(z))/(z-a) = f(a) integral_gamma dd(z)/(z-a) = 2 pi i n(gamma, a) f(a)
$

#thm[
  Cauchy's Integral Formula][
  Let $f(z)$ be analytic on $Delta$ and let $gamma$ be a closed curve in $Delta$. For any $a$ not on $gamma$:
  $
    n(gamma, a) dot f(a) = 1/(2 pi i) integral.cont_gamma (f(z) dd(z))/(z-a)
  $
  if $a in.not Delta$ then obviously both sides are zero.
]
commonly we have $n(gamma, a) = 1$ giving the representation formula:
$
  f(a) = 1/(2 pi i) integral_gamma (f(z) dd(z))/(z-a)
$
if we treat $a$ like a variable (but keeping same index, i.e. making sure the order is constant) then we can conveniently write:
$
  f(z) = 1/(2 pi i) integral_gamma (f(zeta) dd(zeta))/(zeta - z)
$
this is Cauchy's integral formula. Which here is valid for $n(gamma, z) = 1$, when $f(z)$ is analytic in a disk. This representation is very nice and easily lets us determine some local properties of analytic functions, e.g. derivatives. Let $f(z)$ be a function which is analytic in some arbitrary region $Omega$, at a point $a in Omega$ we determine a $delta$-neighborhood $Delta$ contained in $Omega$, and in $Delta$ a circle $C$ about $a$. We can then apply the previous theorem to $f(z)$ in $Delta$. Since $n(C,a) = 1$ we have $n(C,z) = 1$ for all $z in C$. For these $z$ we obtain:
$
  f(z) = 1/(2 pi i) integral_C (f(zeta) dd(zeta))/(zeta - z)
$
if we can differentiate under the integral sign then:
$
  f'(z) = 1/(2 pi i) integral_C (f(zeta) dd(zeta))/(zeta-z)^2
$
this can be done forever:
$
  f^((n)) (z) = n!/(2 pi i) integral_C (f(zeta) dd(zeta))/(zeta-z)^(n+1)
$
If we can justify the differentiations then all derivatives exists at the points in $C$. Since all points in $Omega$ is inside some circle then the derivatives exist in all of $Omega$. To justify these we'll use the following:
#lemma[
  Suppose $phi(zeta)$ is continuous on the arc $gamma$. Then the function:
  $
    F_n (z) = integral_gamma (phi(zeta) dd(zeta))/(zeta-z)^n
  $
  is analytic in each of the regions determined by $gamma$, and its derivative is $F'_n (z) = n F_(n+1) (z)$.
]

#proof[
  First we prove $F_1 (z)$ is continuous. We let $z_0$ be a point not on $gamma$ and choose some neighborhood $abs(z-z_0) < delta$ such that it does not meet $gamma$. Restricting $z$ to a smaller neighborhood $abs(z-z_0) < delta\/2$ then we obtain that $abs(zeta - z) > delta \/2$ for all $zeta in gamma$. Consider:
  $
    F_1 (z) - F_1 (z_0) = (z- z_0) integral_gamma (phi(zeta) dd(zeta))/((zeta-z)(zeta-z_0))
  $
  giving:
  $
    abs(F_1 (z) - F_1 ( z_0)) < abs(z-z_0) 2/delta^2 integral_gamma abs(phi) abs(dd(zeta))
  $
  since $delta$ is arbitrary this proves continuity of $F_1$ at $z_0$. Now consider the difference quotient:
  $
    (F_1 (z) - F_1 (z_0))/(z-z_0) = integral_gamma (phi(zeta)dd(zeta))/((zeta-z)(zeta-z_0))
  $
  by defintion the RHS tends to $F_2 (z_0)$ as $z arrow z_0$, thus $F'_1 (z) = F_2 (z)$. The general case follows from induction. We assume $F'_(n-1) (z) = (n-1) F_n (z)$ and use:
  $
    F_n (z) - F_n (z_0) &= integral_gamma (phi dd(zeta))/((zeta-z)^(n-1)(zeta-z_0)) - integral_gamma (phi dd(zeta))/(zeta-z_0)^n \
    &+ (z-z_0) integral_gamma (phi dd(zeta))/((zeta-z)^n (zeta-z_0))
  $
  by the induction hypothesis the first term two terms cancel as $z arrow z_0$, and in the last term the factor $z-z_0$ is bounded in some neighborhood of $z_0$, thus $F_n$ is continuous. Now if we divide the identity by $z-z_0$ and let $z arrow z_0$ we get:
  $
    F'_n (z_0) =(n-1) F_(n+1) (z_0) + F_(n+1) (z_0) = n F_(n+1) (z_0)
  $
  this is just the induction hypothesis applied to $phi(zeta)\/(zeta-z_0)$. Consider the function:
  $
    G(z) = integral_gamma (phi dd(zeta))/((zeta-z)^(n-1)(zeta-z_0)) tilde F_(n-1)
  $
  the first term is the derivative of this, thus by the induction hypothesis:
  $
    dv(, z) F_(n-1) = (n-1) F_n
  $
  and in the limit $z arrow z_0$ this becomes $(n-1)F_(n+1)$.
]

Thus any analytic function has derivatives of all orders and can be represented by the previous integral formula. This has some nice consequences:

#thm[Morera's theorem][
  If $f(z)$ is defined and continuous in a region $Omega$, and if $integral_gamma f dd(z) = 0$ for all closed curves $gamma$ in $Omega$, then $f(z)$ is analytic in $Omega$.
]

#proof[
  The hypothesis implies that $f(z)$ is the derivative of an analytic function, which then by what we just found implies that $f(z)$ itself is analytic.
]

#thm[Liouville's theorem][
  A function which is analytic and bounded in the whole plane must reduce to a constant.
]
#proof[
  We make use of Cauchy's estimate, letting the radius of $C$ be $r$, and assuming that $abs(f(zeta)) <= M$ on $C$, then letting $z = a$ we have:
  $
         f^((n))(a) & = n!/(2 pi i) integral_C (f(zeta) dd(zeta))/(zeta-a)^(n+1) \
    abs(f^((n))(a)) & <= n! M/(2 pi) integral_C abs(dd(zeta))/abs(zeta-a)^(n+1) \
                    & <= n! M/(2 pi) 1/r^(n+1) integral_C abs(dd(zeta)) \
                    & <= (M n!)/(2 pi) (2 pi r)/r^(n+1) \
    abs(f^((n))(a)) & <= M n! r^(- n)
  $
  for Liouville's theorem we just need $n=1$. The hypothesis means that $abs(f(zeta)) <= M$ on all circles (since it's bounded and analytic), now we can let $r arrow oo$, and Cauchy's estimate then immediately gives $f'(a) = 0$, i.e. the function is constant.
]
As a sidenote this lets us easily prove the fundamental theorem of algebra. Let $P(z)$ be a polynomial of degree $>0$. If $P(z)$ is never zero, then $1\/P(z)$ would be analytic in the whole plane, and since $P(z) arrow oo$ for $z arrow oo$ then $1\/P(z) arrow 0$, this implies boundedness. Then by Liouville's theorem it should be a constant, which it is not, and thus $P(z)=0$ and it must have a root. Note that Cauchy's estimate shows that derivatives of analytic functions are not arbitrary, there must be an $M$ and $r$ such that it is fulfilled. To use it effectively we want to pick a nice $r$, with the purpose being to minimize $M(r) r^(-n)$, with $M(r)$ being the maximum og $abs(f)$ on $abs(zeta-a)=r$.

#pagebreak()
== Local properties of Analytic functions
Before we introduced these exceptional points, which gave us a weaker condition under which Cauchy's theorem would still hold, similarly Cauchy's integral formula remains valid at these points, as long as they don't coincide with $a$. Cauchy's formula gives us a representation of $f(z)$ where the dependence on $z$ is the same as at the exceptional points -- i.e. these points are only exceptional because they lack information, not due to some intrinsic property. These points are called removable singularities.

#thm[
  Let $f(z)$ be analytic in $Omega'$ obtained by omitting a point $a$ from $Omega$. A necessary and sufficient condition that there exist an analytic function in $Omega$ which coincides with $f(z)$ in $Omega'$ is that $lim_(z arrow a) (z-a) f(z) = 0$. This extended function is unique.
]

#proof[
  Necessity and uniqueness follow since the extended function must be continuous at $a$ (i.e. $lim_(z arrow a) (z-a) F(z)=0$, near $a$ $F(z)$ is bounded,). To prove sufficiency we draw a circle $C$ at $a$ such that $C$ and everything inside it is contained in $Omega$. Cauchy's formula holds:
  $
    f(z) = 1/(2 pi i) integral_C (f(zeta)dd(zeta))/(zeta-z)
  $
  for all $z eq.not a$ inside $C$. The integral represents an analytic function of $z$ inside $C$, thus the function which is equal to $f(z)$ for $z eq.not a$ and which has the value:
  $
    1/(2pi i) integral_C (f(zeta)dd(zeta))/(zeta-a)
  $
  for $z=a$ is analytic in $Omega$. Naturally we denote the extended function by $f(z)$ and the value of the previous by $f(a)$.
]



#pagebreak()
= Series and product developments
\* parts of chpt. 5
