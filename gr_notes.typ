#set page(margin: 0.5in)

#let pd(upper, bottom, inline: false) = {
  if inline {
    $partial_(bottom) upper$
  } else {
    $(partial upper)/(partial bottom)$
  }
}
#let pd2(upper, ..bottom) = {
  $(partial^2 upper)/(#{
    for symbol in bottom.pos() [
      $partial symbol$
    ]
  })$
}
#let deriv(..args) = {
  let fn = args.pos().at(0)
  if args.len() == 1 {
    $d / (d fn)$
  } else {
    let unique_vars = ()
    let vars = args.pos().slice(1)
    let derivorder = {
      if vars.len() > 1 { vars.len() }
    }

    for symbol in vars {
      if symbol not in unique_vars {
        unique_vars.push(symbol)
      }
    }

    $(d^derivorder fn) / #{
      for symbol in unique_vars {
        $d symbol^#{
          let deg = vars.filter(x => x == symbol).len()
          if deg > 1 { deg }
        }$
      }
    }$
  }
}

#let pderiv(symbol) = $partial/(partial symbol)$

#let christoffel(top, lbot, rbot) = $Gamma_(lbot rbot)^(top)$
#let metricderivlhs(isymb, jsymb, ksymb) = $pderiv(x^ksymb) g_(isymb jsymb)$
#let metricderivrhs(isymb, jsymb, ksymb) = {
  $christoffel(l, ksymb, isymb) g_(l jsymb) +
  christoffel(l, ksymb, jsymb) g_(l isymb)$
}
#let metricderiv(isymb, jsymb, ksymb) = $metricderivlhs(isymb, jsymb, ksymb) = metricderivrhs(isymb, jsymb, ksymb)$
#let coderiv(bottom, top) = $nabla_bottom top$

= Notes on Tensor Calculus and General Relativity

== Covariant Derivative

The covariant derivative of a vector $V$ is defined as

$
  coderiv(k, V) & = pd(V^i, X^k) arrow(e)_i + V^l christoffel(i, k, l) arrow(e)_i \
                & = (pd(V^i, X^k) + christoffel(i, k, l) V^l)arrow(e)_i \
$

$
  pderiv(X^k) (arrow(V) dot arrow(e)_j) &= (pderiv(X^k) arrow(V)) dot arrow(e)_j + arrow(V) dot (pderiv(X^k) arrow(e)_j)\
  &= (pderiv(X^k) arrow(V)) dot arrow(e)_j + arrow(V) dot (pderiv(X^k) arrow(e)_j)\
  &= (pderiv(X^k) V^i arrow(e)_i) dot arrow(e)_j + V^l e_l dot christoffel(i, k, j) arrow(e)_i\
  &= ((pderiv(X^k) V^i) arrow(e)_i + V^i (pderiv(X^k) arrow(e)_i)) dot arrow(e)_j + V^l e_l dot christoffel(i, k, j) arrow(e)_i\
  &= (pderiv(X^k) V^i) arrow(e)_i dot arrow(e)_j + V^i (pderiv(X^k) arrow(e)_i) dot arrow(e)_j + V^l e_l dot christoffel(i, k, j) arrow(e)_i\
  &= pd(V^i, X^k) g_(i j) + V^i christoffel(l, k, i) g_(l j) + V^l dot christoffel(i, k, j) g_(l i)\
  &= pd(V^i, X^k) g_(i j) + V^l christoffel(i, k, l) g_(i j) + V^l dot christoffel(i, k, j) g_(l i)\
  &= (pd(V^i, X^k) + V^l christoffel(i, k, l)) g_(i j) + V^l dot christoffel(i, k, j) g_(l i)\
  &= (coderiv(k, V^i))g_(i j) + V_i christoffel(i, k, j)\
$

This implies,

$
  coderiv(k, V_j) & = coderiv(k, (V^i g_(i j))) \
                  & = (coderiv(k, V^i)) g_(i j) \
                  & = (pderiv(X^k) V_j) - christoffel(i, k, j) V_i
$

Note that,

$
  coderiv(k, (V^i g_(i j))) & = (coderiv(k, V^i))g_(i j) + V^i (coderiv(k, g_(i j))) \
                            & = (coderiv(k, V^i))g_(i j) quad "(metric compatibility)"
$

== Derivation of Christoffel Symbols in extrinsic space

Let $R(u,v) subset.eq RR^3$ be a parameterization of a surface. A path on this
surface is then given by

$
  R(u(lambda), v(lambda))
$

for $lambda in RR$. Let $x = vec(u(lambda), v(lambda))$, the velocity vectors of
the path at some point $lambda$ is given by
$
  pd(R, lambda) = pd(R, x^i) pd(x^i, lambda)
$

The acceleration vector is given by

$
  deriv(lambda) pd(R, lambda)
  &= deriv(lambda) (pd(R, x^i) pd(x^i, lambda)) \
  &= deriv(lambda)(pd(R, x^i)) dot pd(x^i, lambda) + pd(R, x^i) dot deriv(lambda) (pd(x^i, lambda))
$

Now let

$
  arrow(e)_i = pd(R, x^i)
$

then,

$
  deriv(lambda) arrow(e)_i & = pd(arrow(e)_i, x^j) pd(x^j, lambda) \
                           & = pd2(R, x^j, x^i) pd(x^j, lambda)
$

Substituting back,

$
  deriv(lambda)(pd(R, x^i)) dot pd(x^i, lambda) + pd(R, x^i) dot deriv(lambda) (pd(x^i, lambda))
  &= pd2(R, x^j, x^i) pd(x^j, lambda) dot pd(x^i, lambda) + pd(R, x^i) dot deriv(lambda) (pd(x^i, lambda))\
  &= pd2(R, x^j, x^i) dot pd(x^j, lambda) pd(x^i, lambda) + pd(R, x^i) dot pd2(x^i, lambda)\
$

The vector given by $pd2(R, x^j, x^i)$ is spanned by,

$
  pd(R, x^k) " and " epsilon_(i j k) pd(R, x^j) pd(R, x^k)
$

Notice that $pd(R, x^k)$ form a basis for the tangent plane to the
surface at the point $lambda$. Thus it must span $RR^2$. Furthermore,
$epsilon_(i j k) pd(R, x^j) pd(R, x^k)$ is orthogonal
to basis vectors $pd(R, x^k)$. Therefore, together, they span all
of $RR^3$.

Thus,

$
  pd2(R, x^j, x^i) & = Gamma^k_(i j) pd(R, x^k) +
                     L_(i j) (underbrace(
                         epsilon_(k l m) pd(R, x_l)
                         pd(R, x_m), arrow(n)
                       )) \
                   & = Gamma^k_(i j) pd(R, x^k) +
                     L_(i j) arrow(n) \
$

Solving for $Gamma^k_(i j)$,
$
  &pd2(R, x^j, x^i) dot pd(R, x^l) = Gamma^k_(i j) (pd(R, x^k) dot pd(R, x^l)) +
  L_(i j) underbrace((arrow(n) dot pd(R, x^l)), 0)\
  &=> pd2(R, x^j, x^i) dot pd(R, x^l) = Gamma^k_(i j) (pd(R, x^k) dot pd(R, x^l))\
  &=> pd2(R, x^j, x^i) dot pd(R, x^l) = Gamma^k_(i j) g_(k l)\
  &=> pd2(R, x^j, x^i) dot pd(R, x^l) g^(l m) = Gamma^k_(i j) dot g_(k l) g^(l m) = Gamma^k_(i j)delta_(k)^m = Gamma^m_(i j)
$

== Geodesics (extrinsic version)

Geodesics are the curves on $R$ that have zero tangential acceleration.

$
  deriv(lambda) pd(R, lambda) & = pd2(R, x^j, x^i) dot pd(x^j, lambda) pd(x^i, lambda) + pd(R, x^i) dot pd2(x^i, lambda) \
  &= (christoffel(k, j, i) pd(R, x_k) + L_(i j) arrow(n)) dot pd(x^j, lambda) pd(x^i, lambda) + pd(R, x^i) dot pd2(x^i, lambda) \
  &= christoffel(k, j, i) pd(R, x_k) dot pd(x^j, lambda) pd(x^i, lambda) + L_(i j) arrow(n) dot pd(x^j, lambda) pd(x^i, lambda) + pd(R, x^i) dot pd2(x^i, lambda) \
  &= underbrace(christoffel(k, j, i) pd(R, x_k) dot pd(x^j, lambda) pd(x^i, lambda) + pd(R, x^i) dot pd2(x^i, lambda), "tangential component") + underbrace(L_(i j) arrow(n) dot pd(x^j, lambda) pd(x^i, lambda), "normal component") \
$

Geodesics on $R$ must satisfy

$
  christoffel(k, j, i) pd(R, x_k) dot pd(x^j, lambda) pd(x^i, lambda) + pd(R, x^i) dot pd2(x^i, lambda) = arrow(0)
$

== Geodesics (Intrinsic version)

A geodesic is said to be a curve that parallel transports it's own tangent vector.

A vector that is moved along a curve is said to be parallel transported if

$
  coderiv(k, arrow(V)) = 0
$

Let $arrow(R)(lambda)$ be a curve parameterized by $lambda$. The tangent vector
at point $lambda$ is

$
  V^i (lambda) =(d R^i)/(d lambda)
$


$
  coderiv(k, arrow(V)) &= pd(V^i, lambda) e_i + V^i pd(e_i, lambda)\
  &= pd(V^i, lambda) e_i + V^i pd(e_i, X^k) pd(X^k, lambda)\
  &= pd(V^i, lambda) e_i + V^i christoffel(l, k, i) e_l pd(X^k, lambda)\
  &= pd2(R^i, lambda^2) pd(R^j, X^i) + pd(R^i, lambda) christoffel(l, k, i) pd(R^j, X^l) pd(X^k, lambda) = 0
$


== Metric Compatibility

A connection is called metric compatible if,

$
  nabla (X dot Y) = (nabla X) dot Y + X dot (nabla Y)
$

This is equivalent to saying that the covariant derivative of the metric tensor is $0$,

$
  nabla_k g_(i j) = 0
$

$
  nabla (X dot Y) & = nabla_k g_(i j) X^i Y^j \
                  & = (nabla_k g_(i j)) X^i Y^j + g_(i j) (nabla_k X^i) Y^j + g_(i j) X^i (nabla_k Y^j) \
                  & = (nabla_k g_(i j)) X^i Y^j + (nabla X) dot Y + X dot (nabla Y) \
                  & = (nabla X) dot Y + X dot (nabla Y)
$

Therefore, $nabla_k g_(i j) = 0$ since $X$, $Y$ were assumed to be arbitrary.

== Torsion

A connection is torsion free if,

$
  T(X,Y) = coderiv(X, Y) - coderiv(Y, X) - [X, Y] = 0
$

$[X,Y]$ is the Lie Bracket. It measures the _difference in the change of components_
for the $X$ and $Y$ vector fields when we take a small step in the X then Y compared
to taking a small step in Y then X. The Lie Bracket assumes we have constant basis
vectors -- it does not account for any change in the basis vectors (i.e. curvature).
Whereas, the directional covariant derivatives account for both the change in the
components as well as the basis vectors. When we subtract the former from the
latter, we are measuring the difference in change of the basis vectors themselves.

We see that

$
  coderiv(X, Y) = X^mu ((pd(Y^nu, mu, inline: #true)))e_nu + Y^nu christoffel(l, mu, nu) e_l)
  quad
  coderiv(Y, X) = Y^mu ((pd(X^nu, mu, inline: #true))e_nu + X^nu christoffel(l, mu, nu) e_l)
$

== Derivation of the Christoffel Symbols (Intrinsic Version)

We can derive the expression for the Christoffel symbols given a metric $g_(i j)$.
We do this by first differentiating the metric tensor,


$
  pderiv(x^k) g_(i j) & = pderiv(x^k) (arrow(e)_i dot arrow(e)_j) \
  & = (pderiv(x^k) arrow(e)_i) dot arrow(e)_j + arrow(e)_i dot (pderiv(x^k) arrow(e)_j) quad "(metric compatibility)" \
  & = Gamma_(k i)^l arrow(e)_l dot arrow(e)_j + Gamma_(k j)^l arrow(e)_l dot arrow(e)_i \
  & = Gamma_(k i)^l g_(l j) + Gamma_(k j)^l g_(l i)
$

We can permute the indicies to obtain 3 different equations,

$
  metricderiv(i, j, k) quad "(1)"\
  metricderiv(j, k, i) quad "(2)"\
  metricderiv(k, i, j) quad "(3)"
$

Now, $(1) + (2) - (3)$ gives

$
  metricderivlhs(i, j, k) + metricderivlhs(j, k, i) - metricderivlhs(k, i, j)
  &= metricderivrhs(i, j, k) + metricderivrhs(j, k, i) - (metricderivrhs(k, i, j))\
  &= christoffel(l, k, i) g_(l j) + cancel(christoffel(l, k, j) g_(l i))
  + cancel(christoffel(l, i, j) g_(l k)) + christoffel(l, i, k) g_(l j)
  - cancel(christoffel(l, j, k) g_(l i)) - cancel(christoffel(l, j, i) g_(l k)) quad ("torsion free property: "christoffel(k, i, j) = christoffel(k, j, i))\
  &= 2 christoffel(l, k, i) g_(l j)
$

Therefore we have,

$
  &christoffel(l, k, i) g_(l j) = 1/2 (metricderivlhs(i, j, k) + metricderivlhs(j, k, i) - metricderivlhs(k, i, j)) \
  &arrow.double christoffel(l, k, i) g_(l j) g^(j m) = 1/2 g^(j m)(metricderivlhs(i, j, k) + metricderivlhs(j, k, i) - metricderivlhs(k, i, j)) \
  &arrow.double christoffel(l, k, i) delta_l^m = 1/2 g^(j m)(metricderivlhs(i, j, k) + metricderivlhs(j, k, i) - metricderivlhs(k, i, j)) \
  &arrow.double christoffel(m, k, i) = 1/2 g^(j m)(metricderivlhs(i, j, k) + metricderivlhs(j, k, i) - metricderivlhs(k, i, j)) \
$

== Special Relativity

Special Relativity revolves around flat space-time and the Minkowski Metric

$
  g_(mu nu) = mat(-1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1)
$

We can also write it as

$
  d S^2 = d X^2 + d Y^2 + d Z^2 - d T^2
$


For time like curves, $d S^2 < 0$, and we can denote proper time as

$
  d tau^2 = -d S^2 = d T^2 - d X^2 - d Y^2 - d Z^2
$


=== Constant 4-velocity



=== Uniform Acceleration

Uniform acceleration in Special Relativity has the property that

$
  norm(deriv(X^mu, tau, tau)) = K
$

for some constant $K$. Recall that every time-like path through space-time has
a unit 4-velocity:

$
  norm(deriv(X^mu, tau)) = -1
$
This implies,
$
  g_(mu nu) deriv(X^mu, tau) deriv(X^nu, tau) = -1
$

We can expand as,

$
  (deriv(X, tau))^2 - (deriv(T, tau))^2 = -1
$

we can guess the solution,

$
  deriv(X, tau) = cosh(theta(tau)), quad deriv(T, tau) = sinh(theta(tau))
$

then we have,

$
  deriv(X, tau, tau) = sinh(theta(tau)) deriv(theta, tau), quad deriv(T, tau, tau) = cosh(theta(tau)) deriv(theta, tau)
$

Therefore,

$
  (deriv(X, tau, tau))^2 - (deriv(T, tau, tau))^2 
  &= (sinh(theta(tau)) deriv(theta, tau))^2 - (cosh(theta(tau)) deriv(theta, tau))^2\
  &= sinh^2(theta(tau)) (deriv(theta, tau))^2 - cosh^2(theta(tau)) (deriv(theta, tau))^2\
  &= (sinh^2(theta(tau)) - cosh^2(theta(tau))) (deriv(theta, tau))^2\
  &= -(deriv(theta, tau))^2 = K^2
$

which implies

$
  deriv(theta, tau) = sqrt(-K^2)
$

and

$
  integral d theta = theta(tau) = integral sqrt(-K^2) d tau = tau sqrt(-K^2)
$

=== Euler-Lagrange Equations

$
  deriv(t) (pd(L, dot(X)^mu))= pd(L, X^mu)
$

The Lagrangian, $L$, is given by the "arc-length" of the geodesic

$
  L = -m sqrt(-g_(mu nu)(X) deriv(X^mu, t) deriv(X^nu, t))
$

If we apply the Euler-Lagrange equations, we can show that it is equivalent to
the geodesic differential equation.

$
  deriv(X^mu, tau, tau) = -christoffel(mu, sigma, rho) deriv(X^alpha, tau) deriv(X^rho, tau)
$

First we see that,

$
  deriv(L, X^m) & = -m ((1)/(2 sqrt(-g_(mu nu)(X) deriv(X^mu, t) deriv(X^nu, t))))
                  (
                    (pd(g_(mu nu), m, inline: #true) )deriv(X^mu, t) deriv(X^nu, t)
                    + g_(mu nu) (pd(deriv(X^mu, t), m, inline: #true))deriv(X^nu, t)
                    + g_(mu nu) deriv(X^mu, t)(pd(deriv(X^nu, t), m, inline: #true))
                  ) \
$

But we have,

$
  pd(deriv(X^mu, t), m, inline: #true) & = deriv(t) pd(X^mu, X^m) \
                                       & = deriv(t) delta_m^mu \
                                       & = 0
$

Thus, our equation simplifies to

$
  pd(L, X^m)
  &= m (((pd(g_(mu nu), m, inline: #true)) deriv(X^mu, t) deriv(X^nu, t))/(2 sqrt(-g_(mu nu)(X) deriv(X^mu, t) deriv(X^nu, t))))
$

Now recall that,

$
  dot(X)^mu = deriv(X^mu, t)
$

So we can write

$
  L = -m sqrt(-g_(mu nu)(X) dot(X)^mu dot(X)^nu)
$

Thus, we have that
$
  pd(L, dot(X)^gamma) & = -m 1/(2sqrt(-g_(mu nu)(X) dot(X)^mu dot(X)^nu)) dot g_(mu nu)(X) (deriv(dot(X)^mu, dot(X)^gamma) dot(X)^nu + dot(X)^mu deriv(dot(X)^nu, dot(X)^gamma))\
  &= -m(1/(2sqrt(-g_(mu nu)(X) dot(X)^mu dot(X)^nu))) dot g_(mu nu)(X) (delta^mu_gamma dot(X)^nu + dot(X)^mu delta^nu_gamma)\
  &= -m(1/(2sqrt(-g_(mu nu)(X) dot(X)^mu dot(X)^nu))) dot (delta^mu_gamma dot(X)^nu g_(mu nu)(X) + dot(X)^mu delta^nu_gamma g_(mu nu)(X) )\
  &= -m(1/(2sqrt(-g_(mu nu)(X) dot(X)^mu dot(X)^nu))) dot (2dot(X)_gamma)\
  &= (-m dot dot(X)_gamma)/(sqrt(-g_(mu nu)(X) dot(X)^mu dot(X)^nu))
$

And,

$
  deriv(t) (pd(L, dot(X)^gamma)) &= deriv(t) ((-m dot dot(X)_gamma)/(sqrt(-g_(mu nu)(X) dot(X)^mu dot(X)^nu)))\
  &= -m dot(X)_gamma dot sqrt(-g_(mu nu)(X) dot(X)^mu dot(X)^nu) + m dot(X)_gamma dot 1/(2sqrt(-g_(mu nu)(X) dot(X)^mu dot(X)^nu))
$

=== Principle of Least Action

$$

#pagebreak()
=== Legendre Transform

The Legendre transform, transforms a function $y = f(x)$ to a function $b = g(y')$.
$g$ preserves all the information captured by the function $f$, but is written
in terms of the slope of $y$ at some point $x$ and the $y$-intercept of it's
tangent line.

Given
$
  y = f(x)
$

The slope at some point $x$, is given by,

$
  y' = f'(x)
$

The equation of the tangent line, evaluated at the point $x$, is then

$
  y = f'(x) dot x + b
$

Solving for the $y$-intercept, we have,

$
  b & = y - f'(x) dot x \
    & = y - y' dot x \
$

Now we wish to remove the dependence on $y$ and $x$. We observe that

$
  y = f(x) " and " x = f'^(-1)(y')
$

Thus we can write $y$ in terms of $y'$ as

$
  y = f(f'^(-1)(y'))
$

Thus we have,

$
  b = g(y') = f(f'^(-1)(y')) - y' dot f'^(-1)(y')
$

