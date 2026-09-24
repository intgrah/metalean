
#import "template.typ": *

#let univs(..ls) = $.\{#ls.pos().join($,$)\}$
#let args(..xs) = $(#xs.pos().join($,$))$
#let tuple(..xs) = $(#xs.pos().join($,$))$

#let kw(s) = $bold(upright(#s))$
#let cn(s) = $upright(#s)$ // "Constructor name"

#let axiom = kw("axiom")
#let opaque = kw("opaque")
#let def = kw("def")
#let mutual = kw("mutual")
#let inductive = kw("inductive")
#let where = kw("where")
#let end = kw("end")
#let initQuot(eq) = $kw("init_quot")(#eq)$
#let letE = kw("let")

#let inductives(..sorts) = {
  let multi = sorts.pos().len() > 1
  let q = if multi { $quad$ } else { [] }
  let lines = ()
  if multi { lines.push(mutual) }
  for (head, ..ctors) in sorts.pos() {
    lines.push($#q inductive #head where$)
    for c in ctors { lines.push($#q quad | #c$) }
  }
  if multi { lines.push(end) }
  math.equation(block: true, lines.map(l => $& #l$).join(linebreak()))
}

#let Prop = $"Prop"$
#let Sort(l) = $"Sort"_#l$
#let Type(l) = $"Type"_#l$
#let const(c, ls) = $#c#univs(ls)$
#let forallE(x, t, e) = $forall #x : #t. #e$
#let lam(x, t, e) = $lambda #x : #t. #e$
#let app(..es) = es.pos().join($thin$)
#let letE(x, t, v, e) = $letE #x : #t := #v\; #e$

#let nsort = $n_"sort"$
#let nctor = $n_"ctor"$

#let ind(I, s, ls, ps, idxs) = $#I^#s#univs(ls)#args(ps, idxs)$
#let ctor(I, s, c, ls, ps, fs, rs) = $#I _"ctor"^(#s, #c)#univs(ls)#args(ps, fs, rs)$
#let recr(I, s, ls, lmu, ps, mus, ms, idxs, e) = $#I _"rec"^#s#univs(ls, lmu)#args(ps, mus, ms, idxs, e)$

#let mk = "mk"
#let lift = "lift"
#let ind = "ind"
#let quot(l, alpha, r) = $Q#univs(l)#tuple(alpha, r)$
#let quotMk(l, alpha, r, a) = $Q_mk#univs(l)#tuple(alpha, r, a)$
#let quotLift(la, lb, alpha, r, beta, f, h, a) = $Q_lift#univs($#la, #lb$)#tuple(alpha, r, beta, f, h, a)$
#let quotInd(l, alpha, r, beta, f, a) = $Q_ind#univs(l)#tuple(alpha, r, beta, f, a)$

#let Level = "Level"
#let imax = "imax"
= Syntax

#definition("Levels")[
  $ l in Level ::= u | 0 | l + 1 | max(l, l) | imax(l, l) $
]

#let sem(l) = $lr(bracket.l.stroked #l bracket.r.stroked)$
#definition("Semantics of levels")[
  $
                  sem(-)_- & : Level -> (NN -> NN) -> NN \
                 sem(u)_nu & = nu(u) \
                 sem(0)_nu & = 0 \
             sem(l + 1)_nu & = sem(l)_nu + 1 \
     sem(max(l_1, l_2))_nu & = max(sem(l_1)_nu, sem(l_2)_nu) \
    sem(imax(l_1, l_2))_nu & = cases(0 & "if" sem(l_2)_nu = 0, max(sem(l_1)_nu, sem(l_2)_nu) & "otherwise")
  $

  $
     l_1 = l_2 & <==> forall nu. sem(l_1)_nu = sem(l_2)_nu \
    l_1 <= l_2 & <==> forall nu. sem(l_1)_nu <= sem(l_2)_nu
  $
]

#let Expr = "Expr"
#definition("Expressions")[
  $
    e, t in Expr & ::= x | Sort(l) | const(c, overline(l)) \
    & | forallE(x, t, t) | lam(x, t, e) | app(e, e) | letE(x, t, e, e) \
    & | ind(I, s, overline(l), overline(p), overline(i)) | ctor(I, s, c, overline(l), overline(p), overline(a), overline(r)) | recr(I, s, overline(l), l_mu, overline(p), overline(mu), overline(overline(m)), overline(i), e) \
    & | quot(l, alpha, r) | quotMk(l, alpha, r, a) | quotLift(l_alpha, l_beta, alpha, r, beta, f, h, a) | quotInd(l, alpha, r, beta, f, a)
  $
  We use names for convenience, but use de Bruijn indices in practice.

  We sometimes write $forall x : t_1. t_2$ in the following ways: $Pi x : t_1. t_2$,  $(x : t_1) -> t_2$, and $t_1 -> t_2$ (when $x$ does not occur in $t_2$).
]

#definition("Universe abbreviations")[
  $ Prop := Sort(0) #h(4em) Type(l) := Sort(l + 1) $
]

#let Ctx = "Ctx"
#definition("Contexts")[
  $ Gamma, Delta in Ctx ::= dot | Gamma, x : t $
  We write $(overline(x) : Gamma) -> t$ to mean the multiple abstraction of the type $t$ given by
  $ (x_1 : Gamma_1) -> ... -> (x_n : Gamma_n) -> t. $
]

#let Env = "Env"
#let Entry = "Entry"
#definition("Environments")[
  $
    Epsilon in Env & ::= dot | Epsilon, D \
        D in Entry & ::= axiom const(c, overline(u)) : t \
                   & | opaque const(c, overline(u)) : t \
                   & | def const(c, overline(u)) : t := e \
                   & | mutual inductive I ... end \
                   & | initQuot(I_cn("Eq"))
  $
]

#definition("Inductive types")[
  $
    & mutual \
    & quad inductive const(I^1, overline(u)) med (overline(p) : Gamma_"param") : Gamma_"idx"^1 -> Sort(l) where \
    & quad quad | I_"ctor"^(1, 1) : Gamma_"field"^(1,1) -> overline(R)^(1,1) -> ind(I, 1, overline(u), overline(p), overline(i)^(1,1)) \
    & quad quad dots.v \
    & quad quad | I_"ctor"^(1, nctor^1) : Gamma_"field"^(1,nctor^1) -> overline(R)^(1,nctor^1) -> ind(I, 1, overline(u), overline(p), overline(i)^(1,nctor^1)) \
    & quad dots.v \
    & quad inductive const(I^(nsort), overline(u)) med (overline(p) : Gamma_"param") : Gamma_"idx"^(nsort) -> Sort(l) where \
    & quad quad | I_"ctor"^(nsort, 1) : Gamma_"field"^(nsort,1) -> overline(R)^(nsort,1) -> ind(I, nsort, overline(u), overline(p), overline(i)^(nsort,1)) \
    & quad quad dots.v \
    & quad quad | I_"ctor"^(nsort, nctor^(nsort)) : Gamma_"field"^(nsort,nctor^(nsort)) -> overline(R)^(nsort,nctor^(nsort)) -> ind(I, nsort, overline(u), overline(p), overline(i)^(nsort,nctor^(nsort))) \
    & end \
    & \
    & Gamma_"field"^(s,c) = (a_1 : A_1, dots, a_m : A_m) quad "with levels" quad v_1, dots, v_m \
    & overline(R)^(s,c) = (R^(s,c,1), dots, R^(s,c,n_"rec"^(s,c))) \
    & R^(s,c,g) = Gamma_"rec"^(s,c,g) -> ind(I, s_"rec"^(s,c,g), overline(u), overline(p), overline(j)^(s,c,g))
  $
]
This is the full generality of inductive types!#footnote[Except of course, _nested_ inductive types.] Let's take it apart. First, let us regard every inductive type as belonging to some _mutual_ inductive "block". Even if it is not mutually inductive, we can regard is as being mutual with only itself. We will omit the $mutual$ and $end$ keywords in such a case. We call the mutual inductive's fcomprising inductives its "sorts" (not to be confused with $Sort(u)$!), and we let the variable $1 <= s <= nsort$ range over the possible sorts of an inductive with $nsort$ such sorts. While a mutual inductive with zero sorts is representable, this is not really an issue.#footnote[Because no expression could possibly refer to a mutual inductive with zero sorts.] Here, $I$ refers to the "name" of the _entire_ mutual block. In Lean, mutual blocks are not given names themselves, but rather, the individual sorts are given names. Here, we write $I^s$ to refer to the $s$th sort of a the mutual block with name $I$.

In Lean, every mutual inductive block comes with some universe variables ${overline(u)}$, parameters $(overline(p) : Gamma_"param")$ forming a dependent telescope, and a resulting universe type. These are fixed over all sorts. Additionally, each sort contains some _indices_, also forming a dependent telescope.


#let Nat = cn("Nat")
#let Vector = cn("Vector")
#let cons = cn("cons")
#let nil = cn("nil")
#example("Indexed vectors")[
  #inductives((
    $const(Vector, u) med (alpha : Type(u)) : (n : Nat) -> Prop$,
    $nil : Vector.{u}(alpha, 0)$,
    $cons : (n : Nat) -> alpha -> Vector.{u}(alpha, n) -> Vector.{u}(alpha, n + 1)$,
  ))

  Here, $(alpha : Type(u))$ is a parameter, and $(n : Nat)$ is an index.
]

#let Acc = cn("Acc")
#let intro = cn("intro")
#example("Accessibility")[
  #inductives((
    $Acc.{u} med (alpha : Sort(u)) med (r : alpha -> alpha -> Prop) : (x : alpha) -> Prop$,
    $intro : (x : alpha) -> (forall y : alpha. app(r, y, x) -> Acc.{u}(alpha, r, y)) -> Acc.{u}(alpha, r, x)$,
  ))

  Here, the recursive field is accompanied by a telescope $(y : alpha) -> (h : r y x) -> -$.
]

Each constructor $I_"ctor"^(s,c)$ has three components.

The _ordinary fields_ $Gamma_"field"^(s,c)$ form a dependent telescope over the parameters. Each field may mention the parameters and the fields before it, but not the inductive being defined. In $cons$, the ordinary fields are $(n : Nat)$ and the $alpha$.

The _recursive fields_ $overline(R)^(s,c)$ are the only place where the block refers to itself. Each $R^(s,c,g)$ has its own telescope of arguments $Gamma_"rec"^(s,c,g)$, which may mention the parameters and all of the ordinary fields, and ends in some sort $s_"rec"^(s,c,g)$ of the same block, at the same universe variables ${overline(u)}$ and parameters $overline(p)$, with indices $overline(j)^(s,c,g)$. Strict positivity holds by construction! Why do we say that recursive fields come last? It is actually impossible for a recursive field to be _depended_ on without violating strict positivity, so the recursive fields are independent of one another and form a tuple, and we may assume that they all come after the ordinary fields.

#proposition("Recursive fields cannot be depended on usefully")[
  Let $x : (overline(y) : Gamma_"rec") -> ind(I, s, overline(u), overline(p), overline(j))$ be a recursive field of a constructor, and let $t$ be the type of a later field, in $beta$-normal form. If $x$ occurs in $t$, then $I$ occurs in $t$ at a negative position.
]

#proof[
  A term whose type ends in $I$ can only be used by passing it to something whose domain ends in $I$.#footnote[By no-confusion, to be proven!] Nothing in scope has such a domain: the types of constants, parameters, non-recursive fields and $I$ itself cannot mention $I$, and positivity forbids it in the domains of recursive fields. So wherever $x$ occurs in $t$, the domain it is passed to must acquire $I$ from $t$ itself, which puts $I$ in $t$ at a negative position.
]

Why did we require that $t$ is in $beta$-normal form? consider the following inductive type, which is accepted by Lean:

#[
  #let N = cn("N")
  #let mk = cn("mk")
  #let Nat = cn("Nat")
  #inductives((
    $#N : Type(0)$,
    $mk : (x : #N) -> app((lam(x, #N, Nat)), x) -> #N$,
  ))

  $#N$ occurs negatively, but it does not occur negatively in a _useful_ way, which is evident once the $beta$-redex is reduced. It follows that, if $x$ occurs in $t$, not in $beta$-normal form, $b$-normalising $t$ deletes $x$, showing that $x$ was never really useful in the first place.
]

Despite this fact, Lean allows non-recursive and recursive fields to be interleaved. For simplicity, our syntax does _not_ allow interleaving, and outright _disallows_ recursive fields to be depended on. To be able to consume the same input as Lean, we perform a frontend translation that sifts all recursive fields to the end, thereby weakening the contexts in which their types were defined in.

The _target indices_ $overline(i)^(s,c)$ give the indices at which the constructor lands. They may mention the parameters and the ordinary fields, but not the recursive fields. In $cn("cons")$, the target index is $n + 1$, while the recursive field has index $n$.

#example("Even and odd")[
  #let Even = cn("Even")
  #let Odd = cn("Odd")
  #let zero = cn("zero")
  #let succ = cn("succ")
  #let Nat = cn("Nat")
  #inductives(
    (
      $Even : (n : Nat) -> Prop$,
      $zero : Even(0)$,
      $succ : (n : Nat) -> Odd(n) -> Even(n + 1)$,
    ),
    (
      $Odd : (n : Nat) -> Prop$,
      $succ : (n : Nat) -> Even(n) -> Odd(n + 1)$,
    ),
  )

  Here $Even$ and $Odd$ are the two sorts of one block. The recursive field of $Even"."succ$ lands in $Odd$, and that of $Odd"."succ$ lands in $Even$.
]

#let vdash = $scripts(tack)$
#let Ind(s, ls, ps, idxs) = $I^#s#univs(ls)#args(ps, idxs)$

= Typing

#definition("Substitution and instantiation")[
  We write $e[overline(a) slash overline(x)]$ for simultaneous capture-avoiding substitution and $e{overline(l) slash overline(u)}$ for the instantiation of universe variables. These are defined in the obvious way and so their definitions are not given here. We write $l_I$ for the resulting level of $I$.
]

#judgement([definitional equality], $Epsilon[Gamma] tack e_1 equiv e_2 : t$)[
  The judgement is relative to a fixed list of universe variables $overline(u)$, over which the levels in $Gamma$, $e_1$, $e_2$ and $t$ range. We define the usual typing $Epsilon[Gamma] tack e : t$ as the diagonal $Epsilon[Gamma] tack e equiv e : t$. For $Delta = (x_1 : t_1, dots, x_n : t_n)$, $Epsilon[Gamma] tack overline(a) equiv overline(b) : Delta$ abbreviates the premises $Epsilon[Gamma] tack a_k equiv b_k : t_k [a_1, dots, a_(k-1) slash x_1, dots, x_(k-1)]$ for each $k$, and $Epsilon[Gamma] tack overline(a) : Delta$ abbreviates $Epsilon[Gamma] tack overline(a) equiv overline(a) : Delta$.

  #rules(
    rule(name: [symm], $Epsilon[Gamma] tack e_1 equiv e_2 : t$, $Epsilon[Gamma] tack e_2 equiv e_1 : t$),
    rule(
      name: [trans],
      $Epsilon[Gamma] tack e_1 equiv e_2 : t$,
      $Epsilon[Gamma] tack e_2 equiv e_3 : t$,
      $Epsilon[Gamma] tack e_1 equiv e_3 : t$,
    ),
    rule(name: [var], $(x : t) in Gamma$, $Epsilon[Gamma] tack t : Sort(l)$, $Epsilon[Gamma] tack x : t$),
    rule(
      name: [conv],
      $Epsilon[Gamma] tack t_1 equiv t_2 : Sort(l)$,
      $Epsilon[Gamma] tack e_1 equiv e_2 : t_1$,
      $Epsilon[Gamma] tack e_1 equiv e_2 : t_2$,
    ),
    rule(name: [sort], $Epsilon[Gamma] tack Sort(l) : Sort(l + 1)$),
    rule(
      name: [const],
      $([def,opaque,axiom] c.{overline(u)} : t) in Epsilon$,
      $Epsilon[Gamma] tack t{overline(l) slash overline(u)} : Sort(v)$,
      $Epsilon[Gamma] tack c.{overline(l)} : t{overline(l) slash overline(u)}$,
    ),
    rule(
      name: [const-$delta$],
      $(def c.{overline(u)} : t := e) in Epsilon$,
      $Epsilon[Gamma] tack t{overline(l) slash overline(u)} : Sort(v)$,
      $Epsilon[Gamma] tack e{overline(l) slash overline(u)} : t{overline(l) slash overline(u)}$,
      $Epsilon[Gamma] tack c.{overline(l)} equiv e{overline(l) slash overline(u)} : t{overline(l) slash overline(u)}$,
    ),
  )
  #rules(
    rule(
      name: [$forall$-form],
      $Epsilon[Gamma] tack t_1 equiv t_2 : Sort(l_1)$,
      $Epsilon[Gamma, x : t_1] tack t'_1 equiv t'_2 : Sort(l_2)$,
      $Epsilon[Gamma, x : t_2] tack t'_1 equiv t'_2 : Sort(l_2)$,
      $Epsilon[Gamma] tack forallE(x, t_1, t'_1) equiv forallE(x, t_2, t'_2) : Sort(imax(l_1, l_2))$,
    ),
    rule(
      name: [$forall$-intro],
      $Epsilon[Gamma] tack t_1 equiv t_2 : Sort(l_1)$,
      [#stack(
        spacing: 0.6em,
        $Epsilon[Gamma, x : t_1] tack t' : Sort(l_2)$,
        $Epsilon[Gamma, x : t_2] tack t' : Sort(l_2)$,
      )],
      [#stack(
        spacing: 0.6em,
        $Epsilon[Gamma, x : t_1] tack e_1 equiv e_2 : t'$,
        $Epsilon[Gamma, x : t_2] tack e_1 equiv e_2 : t'$,
      )],
      $Epsilon[Gamma] tack lam(x, t_1, e_1) equiv lam(x, t_2, e_2) : forallE(x, t_1, t')$,
    ),
    rule(
      name: [$forall$-elim],
      [#stack(spacing: 0.6em, $Epsilon[Gamma] tack t : Sort(l_1)$, $Epsilon[Gamma, x : t] tack t' : Sort(l_2)$)],
      [#stack(
        spacing: 0.6em,
        $Epsilon[Gamma] tack f_1 equiv f_2 : forallE(x, t, t')$,
        $Epsilon[Gamma] tack a_1 equiv a_2 : t$,
      )],
      $Epsilon[Gamma] tack t'[a_1 slash x] equiv t'[a_2 slash x] : Sort(l_2)$,
      $Epsilon[Gamma] tack app(f_1, a_1) equiv app(f_2, a_2) : t'[a_1 slash x]$,
    ),
    rule(
      name: [$forall$-$beta$],
      [#stack(
        spacing: 0.6em,
        $Epsilon[Gamma] tack t : Sort(l_1)$,
        $Epsilon[Gamma, x : t] tack t' : Sort(l_2)$,
        $Epsilon[Gamma, x : t] tack e' : t'$,
      )],
      [#stack(
        spacing: 0.6em,
        $Epsilon[Gamma] tack e : t$,
        $Epsilon[Gamma] tack t'[e slash x] : Sort(l_2)$,
        $Epsilon[Gamma] tack e'[e slash x] : t'[e slash x]$,
      )],
      $Epsilon[Gamma] tack app((lam(x, t, e')), e) equiv e'[e slash x] : t'[e slash x]$,
    ),
    rule(
      name: [$forall$-$eta$],
      [#stack(
        spacing: 0.6em,
        $Epsilon[Gamma] tack t : Sort(l_1)$,
        $Epsilon[Gamma, x : t] tack t' : Sort(l_2)$,
        $Epsilon[Gamma, x : t] tack t : Sort(l_1)$,
      )],
      [#stack(
        spacing: 0.6em,
        $Epsilon[Gamma, x : t] tack e : forallE(y, t, t'[y slash x])$,
        $Epsilon[Gamma] tack e : forallE(x, t, t')$,
      )],
      $Epsilon[Gamma] tack lam(x, t, app(e, x)) equiv e : forallE(x, t, t')$,
    ),
    rule(
      name: [let-$zeta$#footnote[Congruence for let-expressions is derivable]],
      $Epsilon[Gamma] tack t : Sort(l_1)$,
      $Epsilon[Gamma] tack v : t$,
      $Epsilon[Gamma] tack r : Sort(l_2)$,
      $Epsilon[Gamma] tack e'[v slash x] : r$,
      $Epsilon[Gamma] tack letE(x, t, v, e') equiv e'[v slash x] : r$,
    ),
    rule(
      name: [proof-irrel],
      $Epsilon[Gamma] tack p : Prop$,
      $Epsilon[Gamma] tack h_1 : p$,
      $Epsilon[Gamma] tack h_2 : p$,
      $Epsilon[Gamma] tack h_1 equiv h_2 : p$,
    ),
  )
  #rules(
    rule(
      name: [ind-form],
      $I in Epsilon$,
      $Epsilon[Gamma] tack overline(p)_1 equiv overline(p)_2 : Gamma_"param"$,
      $Epsilon[Gamma] tack overline(i)_1 equiv overline(i)_2 : Gamma_"idx"^s (overline(p)_1)$,
      $Epsilon[Gamma] tack Ind(s, overline(l), overline(p)_1, overline(i)_1) equiv Ind(s, overline(l), overline(p)_2, overline(i)_2) : Sort(l_I {overline(l) slash overline(u)})$,
    ),
    rule(
      name: [ind-intro],
      [#stack(
        spacing: 0.6em,
        $I in Epsilon$,
        $Epsilon[Gamma] tack overline(p)_1 equiv overline(p)_2 : Gamma_"param"$,
        $Epsilon[Gamma] tack overline(a)_1 equiv overline(a)_2 : Gamma_"field"^(s,c) (overline(p)_1)$,
        $forall g. thin Epsilon[Gamma] tack r_(1,g) equiv r_(2,g) : R^(s,c,g) (overline(p)_1, overline(a)_1)$,
        $forall f. thin Epsilon[Gamma] tack A_f (overline(p)_1, overline(a)_1) equiv A_f (overline(p)_2, overline(a)_2) : Sort(w_f)$,
        $forall g. thin Epsilon[Gamma] tack R^(s,c,g) (overline(p)_1, overline(a)_1) equiv R^(s,c,g) (overline(p)_2, overline(a)_2) : Sort(w'_g)$,
        $Epsilon[Gamma] tack Ind(s, overline(l), overline(p)_1, overline(i)^(s,c) (overline(p)_1, overline(a)_1)) equiv Ind(s, overline(l), overline(p)_2, overline(i)^(s,c) (overline(p)_2, overline(a)_2)) : Sort(l_I {overline(l) slash overline(u)})$,
      )],
      $Epsilon[Gamma] tack ctor(I, s, c, overline(l), overline(p)_1, overline(a)_1, overline(r)_1) equiv ctor(I, s, c, overline(l), overline(p)_2, overline(a)_2, overline(r)_2) : Ind(s, overline(l), overline(p)_1, overline(i)^(s,c) (overline(p)_1, overline(a)_1))$,
    ),
  )
  #rules(
    aside([large elimination])[
      #rules(
        rule(name: [large], $1 <= l_I$, $tack I^s "large"$),
        rule(
          name: [subsingleton#footnote[Lean _also_ requires $nsort = 1$, but this is not actually necessary, so we omit it here.]],
          $nctor^s <= 1$,
          $forall c, f. thin v_f^(s,c) = 0 or exists k. thin i_k^(s,c) = a_f$,
          $forall c. thin n_"rec"^(s,c) = 0 or l_I = 0$,
          $tack I^s "large"$,
        ),
      )
    ],
    rule(
      name: [ind-elim],
      [#stack(
        spacing: 0.6em,
        $I in Epsilon$,
        $v = 0 quad or quad forall s'. thin tack I^(s') "large"$,
        $Epsilon[Gamma] tack overline(p)_1 equiv overline(p)_2 : Gamma_"param"$,
        $forall s'. thin Epsilon[Gamma] tack mu_1^(s') equiv mu_2^(s') : (overline(i) : Gamma_"idx"^(s') (overline(p)_1)) -> Ind(s', overline(l), overline(p)_1, overline(i)) -> Sort(v)$,
        $forall s', c. thin Epsilon[Gamma] tack m_1^(s',c) equiv m_2^(s',c) : (overline(a) : Gamma_"field"^(s',c) (overline(p)_1)) -> (overline(r) : overline(R)^(s',c) (overline(p)_1, overline(a))) \
        quad -> ((overline(y) : Gamma_"rec"^(s',c,g) (overline(p)_1, overline(a))) -> app(mu_1^(s_"rec"^(s',c,g)), overline(j)^(s',c,g) (overline(p)_1, overline(a)), app(r_g, overline(y))))_g \
        quad -> app(mu_1^(s'), overline(i)^(s',c) (overline(p)_1, overline(a)), ctor(I, s', c, overline(l), overline(p)_1, overline(a), overline(r)))$,
        $Epsilon[Gamma] tack overline(i)_1 equiv overline(i)_2 : Gamma_"idx"^s (overline(p)_1)$,
        $Epsilon[Gamma] tack x_1 equiv x_2 : Ind(s, overline(l), overline(p)_1, overline(i)_1)$,
        $Epsilon[Gamma] tack app(mu_1^s, overline(i)_1, x_1) equiv app(mu_2^s, overline(i)_2, x_2) : Sort(v)$,
      )],
      $Epsilon[Gamma] tack recr(I, s, overline(l), v, overline(p)_1, overline(mu)_1, overline(overline(m))_1, overline(i)_1, x_1) equiv recr(I, s, overline(l), v, overline(p)_2, overline(mu)_2, overline(overline(m))_2, overline(i)_2, x_2) : app(mu_1^s, overline(i)_1, x_1)$,
    ),
  )
  #rules(
    aside([$iota$-reduction])[
      $
        "lhs"^(s,c) & = recr(I, s, overline(l), v, overline(p), overline(mu), overline(overline(m)), overline(i)^(s,c) (overline(p), overline(a)), ctor(I, s, c, overline(l), overline(p), overline(a), overline(r))) \
        "rhs"^(s,c) & = app(m^(s,c), overline(a), overline(r), (lambda overline(y) : Gamma_"rec"^(s,c,g) (overline(p), overline(a)). recr(I, s_"rec"^(s,c,g), overline(l), v, overline(p), overline(mu), overline(overline(m)), overline(j)^(s,c,g) (overline(p), overline(a)), app(r_g, overline(y))))_g) \
        T^(s,c) & = app(mu^s, overline(i)^(s,c) (overline(p), overline(a)), ctor(I, s, c, overline(l), overline(p), overline(a), overline(r)))
      $
    ],
    rule(
      name: [$iota$],
      [#stack(
        spacing: 0.6em,
        $I in Epsilon$,
        $v = 0 or forall s'. thin tack I^(s') "large"$,
        $Epsilon[Gamma] tack overline(p) : Gamma_"param"$,
        $forall s'. thin Epsilon[Gamma] tack mu^(s') : (overline(i) : Gamma_"idx"^(s') (overline(p))) -> Ind(s', overline(l), overline(p), overline(i)) -> Sort(v)$,
        $forall s', c'. thin Epsilon[Gamma] tack m^(s',c') : (overline(a) : Gamma_"field"^(s',c') (overline(p))) -> (overline(r) : overline(R)^(s',c') (overline(p), overline(a))) \
        quad -> ((overline(y) : Gamma_"rec"^(s',c',g) (overline(p), overline(a))) -> app(mu^(s_"rec"^(s',c',g)), overline(j)^(s',c',g) (overline(p), overline(a)), app(r_g, overline(y))))_g \
        quad -> app(mu^(s'), overline(i)^(s',c') (overline(p), overline(a)), ctor(I, s', c', overline(l), overline(p), overline(a), overline(r)))$,
        $Epsilon[Gamma] tack overline(a) : Gamma_"field"^(s,c) (overline(p))$,
        $forall g. thin Epsilon[Gamma] tack r_g : R^(s,c,g) (overline(p), overline(a))$,
        $Epsilon[Gamma] tack T^(s,c) : Sort(v)$,
        $Epsilon[Gamma] tack "lhs"^(s,c) : T^(s,c)$,
        $Epsilon[Gamma] tack "rhs"^(s,c) : T^(s,c)$,
      )],
      $Epsilon[Gamma] tack "lhs"^(s,c) equiv "rhs"^(s,c) : T^(s,c)$,
    ),
  )
  #rules(
    aside([structures])[
      $tack I_"ctor"^(s,c) "struct"$ is a _structure constructor_ if $I$ has the single sort $s$, $s$ has the single constructor $c$, no indices and no recursive fields, and $tack I^s "large"$.

      Define the projections of fields and the $eta$-expansion as follows:
      $
        pi_f (x) & = recr(I, s, overline(l), v_f {overline(l) slash overline(u)}, overline(p), lambda z. A_f (overline(p), pi_1 (z), dots, pi_(f-1) (z)), lambda overline(a). a_f, (), x) \
        eta(x) & = ctor(I, s, c, overline(l), overline(p), #($pi_1 (x), dots, pi_m (x)$), ())
      $
    ],
    rule(
      name: [struct-$eta$],
      $I in Epsilon$,
      $tack I_"ctor"^(s,c) "struct"$,
      $Epsilon[Gamma] tack overline(p) : Gamma_"param"$,
      $Epsilon[Gamma] tack x : Ind(s, overline(l), overline(p), ())$,
      $Epsilon[Gamma] tack eta(x) : Ind(s, overline(l), overline(p), ())$,
      $Epsilon[Gamma] tack eta(x) equiv x : Ind(s, overline(l), overline(p), ())$,
    ),
  )
  #rules(
    rule(
      name: [quot-form],
      $initQuot(I_cn("Eq")) in Epsilon$,
      $Epsilon[Gamma] tack alpha_1 equiv alpha_2 : Sort(l)$,
      $Epsilon[Gamma] tack r_1 equiv r_2 : alpha_1 -> alpha_1 -> Prop$,
      $Epsilon[Gamma] tack quot(l, alpha_1, r_1) equiv quot(l, alpha_2, r_2) : Sort(l)$,
    ),
    rule(
      name: [quot-intro],
      $initQuot(I_cn("Eq")) in Epsilon$,
      $Epsilon[Gamma] tack alpha_1 equiv alpha_2 : Sort(l)$,
      $Epsilon[Gamma] tack r_1 equiv r_2 : alpha_1 -> alpha_1 -> Prop$,
      $Epsilon[Gamma] tack a_1 equiv a_2 : alpha_1$,
      $Epsilon[Gamma] tack quotMk(l, alpha_1, r_1, a_1) equiv quotMk(l, alpha_2, r_2, a_2) : quot(l, alpha_1, r_1)$,
    ),
    rule(
      name: [quot-elim],
      [#stack(
        spacing: 0.6em,
        $initQuot(I_cn("Eq")) in Epsilon$,
        $Epsilon[Gamma] tack alpha_1 equiv alpha_2 : Sort(l_1)$,
        $Epsilon[Gamma] tack r_1 equiv r_2 : alpha_1 -> alpha_1 -> Prop$,
        $Epsilon[Gamma] tack beta_1 equiv beta_2 : Sort(l_2)$,
        $Epsilon[Gamma] tack f_1 equiv f_2 : alpha_1 -> beta_1$,
        $Epsilon[Gamma] tack h_1 equiv h_2 : forall a thin b : alpha_1. app(r_1, a, b) -> I_cn("Eq").{l_2}(beta_1, app(f_1, a), app(f_1, b))$,
        $Epsilon[Gamma] tack a_1 equiv a_2 : quot(l_1, alpha_1, r_1)$,
      )],
      $Epsilon[Gamma] tack quotLift(l_1, l_2, alpha_1, r_1, beta_1, f_1, h_1, a_1) equiv quotLift(l_1, l_2, alpha_2, r_2, beta_2, f_2, h_2, a_2) : beta_1$,
    ),
    rule(
      name: [quot-ind],
      [#stack(
        spacing: 0.6em,
        $initQuot(I_cn("Eq")) in Epsilon$,
        $Epsilon[Gamma] tack alpha_1 equiv alpha_2 : Sort(l)$,
        $Epsilon[Gamma] tack r_1 equiv r_2 : alpha_1 -> alpha_1 -> Prop$,
        $Epsilon[Gamma] tack beta_1 equiv beta_2 : quot(l, alpha_1, r_1) -> Prop$,
        $Epsilon[Gamma] tack f_1 equiv f_2 : forall a : alpha_1. app(beta_1, quotMk(l, alpha_1, r_1, a))$,
        $Epsilon[Gamma] tack a_1 equiv a_2 : quot(l, alpha_1, r_1)$,
        $Epsilon[Gamma] tack app(beta_1, a_1) equiv app(beta_2, a_2) : Prop$,
      )],
      $Epsilon[Gamma] tack quotInd(l, alpha_1, r_1, beta_1, f_1, a_1) equiv quotInd(l, alpha_2, r_2, beta_2, f_2, a_2) : app(beta_1, a_1)$,
    ),
    rule(
      name: [quot-$iota$],
      [#stack(
        spacing: 0.6em,
        $initQuot(I_cn("Eq")) in Epsilon$,
        $Epsilon[Gamma] tack alpha : Sort(l_1)$,
        $Epsilon[Gamma] tack r : alpha -> alpha -> Prop$,
        $Epsilon[Gamma] tack beta : Sort(l_2)$,
        $Epsilon[Gamma] tack f : alpha -> beta$,
        $Epsilon[Gamma] tack h : forall a thin b : alpha. app(r, a, b) -> I_cn("Eq").{l_2}(beta, app(f, a), app(f, b))$,
        $Epsilon[Gamma] tack a : alpha$,
        $Epsilon[Gamma] tack quotLift(l_1, l_2, alpha, r, beta, f, h, quotMk(l_1, alpha, r, a)) : beta$,
        $Epsilon[Gamma] tack app(f, a) : beta$,
      )],
      $Epsilon[Gamma] tack quotLift(l_1, l_2, alpha, r, beta, f, h, quotMk(l_1, alpha, r, a)) equiv app(f, a) : beta$,
    ),
  )
]

#judgement([well-typed substitutions], $Epsilon[Delta] tack sigma : Gamma$)[
  #rules(
    rule($forall (x : t) in Gamma. thin Epsilon[Delta] tack sigma(x) : t[sigma]$, $Epsilon[Delta] tack sigma : Gamma$),
    rule(
      $forall (x : t) in Gamma. thin Epsilon[Delta] tack sigma_1 (x) equiv sigma_2 (x) : t[sigma_1]$,
      $Epsilon[Delta] tack sigma_1 equiv sigma_2 : Gamma$,
    ),
  )
]

#judgement([well-formedness of types], $Epsilon[Gamma] tack t "type"$)[
  #rules(
    rule($Epsilon[Gamma] tack t : Sort(u)$, $Epsilon[Gamma] tack t "type"$),
  )
]

#judgement(
  [type equality#footnote[We can't use the transitivity of definitional equality here, because three types may be pairwise equal but at different universe sorts. Only with uniqueness of sorts, proved much later, can we conclude that they are really the same.]],
  $Epsilon[Gamma] tack t_1 equiv t_2 "type"$,
)[
  #rules(
    rule($Epsilon[Gamma] tack t_1 equiv t_2 : Sort(u)$, $Epsilon[Gamma] tack t_1 equiv t_2 "type"$),
    rule(
      $Epsilon[Gamma] tack t_1 equiv t_2 "type"$,
      $Epsilon[Gamma] tack t_2 equiv t_3 "type"$,
      $Epsilon[Gamma] tack t_1 equiv t_3 "type"$,
    ),
  )
]

#judgement([well-formedness of contexts], $Epsilon tack Gamma "ctx"$)[
  #rules(
    rule($Epsilon tack dot "ctx"$),
    rule($Epsilon tack Gamma "ctx"$, $Epsilon[Gamma] tack t "type"$, $Epsilon tack Gamma, x : t "ctx"$),
  )
]

#judgement([conditional well-formedness of telescopes], $Epsilon[Gamma] vdash_P Delta "tele"$)[
  For a predicate $P$ on levels,
  #rules(
    rule($Epsilon[Gamma] vdash_P dot "tele"$),
    rule(
      $Epsilon[Gamma] vdash_P Delta "tele"$,
      $Epsilon[Gamma, Delta] tack t : Sort(u)$,
      $P(u)$,
      $Epsilon[Gamma] vdash_P Delta, x : t "tele"$,
    ),
  )
]


#given[Fix a mutual inductive block $I$ with universe variables $overline(u)$, parameters $(overline(p) : Gamma_"param")$, index telescopes $Gamma_"idx"^s$ and resulting universe $Sort(l)$. Write $P_I (v) <==> imax(v, l) <= l$.#footnote[This is _more_ permissive than Lean, but it is still sound.]][

  #judgement([well-formedness of (non-recursive) fields], $Epsilon[Gamma] vdash_I (A, v) "field"$)[
    #rules(
      rule($Epsilon[Gamma] tack A : Sort(v)$, $P_I (v)$, $Epsilon[Gamma] vdash_I (A, v) "field"$),
    )
    where $(A, v)$ is an ordinary field with its level.
  ]

  #judgement([well-formedness of recursive fields], $Epsilon[Gamma] vdash_I R "recfield"$)[
    #rules(
      rule(
        $Epsilon[Gamma] vdash_(P_I) Theta "tele"$,
        $Epsilon[Gamma, Theta] tack overline(j) : Gamma_"idx"^s$,
        $Epsilon[Gamma] vdash_I Theta -> I^s.{overline(u)}(overline(p), overline(j)) "recfield"$,
      ),
    )
  ]

  #judgement([well-formedness of constructors], $Epsilon vdash_I I_"ctor"^(s,c) "ctor"$)[
    For $I_"ctor"^(s,c)$ with ordinary fields $(a_1 : A_1), dots, (a_m : A_m)$ at levels $v_1, dots, v_m$, recursive fields $R_1, dots, R_k$ and target indices $overline(i)$,
    #rules(
      rule(
        $forall f. thin Epsilon[Gamma_"param", a_1 : A_1, dots, a_(f-1) : A_(f-1)] vdash_I (A_f, v_f) "field"$,
        $forall g. thin Epsilon[Gamma_"param", Gamma_"field"^(s,c)] vdash_I R_g "recfield"$,
        $Epsilon[Gamma_"param", Gamma_"field"^(s,c)] tack overline(i) : Gamma_"idx"^s$,
        $Epsilon vdash_I I_"ctor"^(s,c) "ctor"$,
      ),
    )
  ]

  #judgement([well-formedness of inductive blocks], $Epsilon tack I "inductive"$)[
    #rules(
      rule(
        $Epsilon[dot] tack Gamma_"param" "tele"$,
        $forall s. thin Epsilon[Gamma_"param"] tack Gamma_"idx"^s "tele"$,
        $forall s, c. thin Epsilon vdash_I I_"ctor"^(s,c) "ctor"$,
        $Epsilon tack I "inductive"$,
      ),
    )
  ]
]

#let Eq = cn("Eq")
#let refl = cn("refl")
#[
  #definition("Equality")[
    #inductives((
      $Eq.{u} med (alpha : Sort(u)) med (a : alpha) : (b : alpha) -> Prop$,
      $refl : Eq.{u}(alpha, a, a)$,
    ))
  ]

  #judgement([well-formedness of environment entries], $Epsilon tack D "entry"$)[
    #rules(
      rule($Epsilon[dot] tack t "type"$, $Epsilon tack axiom const(c, overline(u)) : t "entry"$),
      rule(
        $Epsilon[dot] tack t "type"$,
        $Epsilon[dot] tack e : t$,
        $Epsilon tack opaque const(c, overline(u)) : t "entry"$,
      ),
      rule(
        $Epsilon[dot] tack t "type"$,
        $Epsilon[dot] tack e : t$,
        $Epsilon tack def const(c, overline(u)) : t := e "entry"$,
      ),
      rule($Epsilon tack I "inductive"$, $Epsilon tack mutual inductive I ... end "entry"$),
      rule($Epsilon(I_Eq) = Eq$, $Epsilon tack initQuot(I_Eq) "entry"$),
    )
  ]
]

#judgement([well-formedness of environments], $tack Epsilon "env"$)[
  #rules(
    rule($tack dot "env"$),
    rule($tack Epsilon "env"$, $Epsilon tack D "entry"$, $tack Epsilon, D "env"$),
  )
]

= Metatheory

#lemma("Regularity")[
  If $Epsilon[Gamma] tack e_1 equiv e_2 : t$, then $Epsilon[Gamma] tack e_1 : t$, $Epsilon[Gamma] tack e_2 : t$ and $Epsilon[Gamma] tack t "type"$.
]

#proof[
  #smallcaps[symm], #smallcaps[trans], and induction on the typing derivation.
]

#lemma("Environment extension")[
  Let $Epsilon$ be a prefix of $Epsilon'$. If $Epsilon[Gamma] tack e_1 equiv e_2 : t$, then $Epsilon'[Gamma] tack e_1 equiv e_2 : t$, and if $Epsilon tack Gamma "ctx"$, then $Epsilon' tack Gamma "ctx"$.
]

#proof[
  The first is by induction on the typing derivation of $Epsilon[Gamma] tack e_1 equiv e_2 : t$. The second is by induction on the derivation of $Epsilon tack Gamma "ctx"$, using the first.
]

#lemma("Level instantiation")[
  Let $overline(l)$ be levels. If $Epsilon[Gamma] tack e_1 equiv e_2 : t$, then $Epsilon[Gamma{overline(l) slash overline(u)}] tack e_1 {overline(l) slash overline(u)} equiv e_2 {overline(l) slash overline(u)} : t{overline(l) slash overline(u)}$, and if $Epsilon tack Gamma "ctx"$, then $Epsilon tack Gamma{overline(l) slash overline(u)} "ctx"$.
]

#proof[
  The first is by induction on the typing derivation of $Epsilon[Gamma] tack e_1 equiv e_2 : t$. The second is by induction on the derivation of $Epsilon tack Gamma "ctx"$, using the first.
]

#lemma("Weakening")[
  If $Epsilon[Gamma_1, Gamma_2] tack e_1 equiv e_2 : t$ and $y$ is fresh, then $Epsilon[Gamma_1, y : t', Gamma_2] tack e_1 equiv e_2 : t$.
]

#lemma("Substitution")[
  If $Epsilon[Delta] tack sigma : Gamma$ and $Epsilon[Gamma] tack e_1 equiv e_2 : t$, then $Epsilon[Delta] tack e_1 [sigma] equiv e_2 [sigma] : t[sigma]$.
]

#proof[
  Weakening and substitution are proved together, by induction on the typing derivation of $Epsilon[Gamma] tack e_1 equiv e_2 : t$, for substitutions sending each variable either to a variable of the same type or to a term of the substituted type.
]

#lemma("Context conversion")[
  If $Epsilon[Gamma] tack t_1 equiv t_2 : Sort(l)$ and $Epsilon[Gamma, x : t_1] tack e_1 equiv e_2 : t$, then $Epsilon[Gamma, x : t_2] tack e_1 equiv e_2 : t$.
]

#proof[
  The identity substitution from $Gamma, x : t_1$ to $Gamma, x : t_2$ is of the form above, typing $x$ by #smallcaps[conv].
]

#lemma("Substitution congruence")[
  If $Epsilon tack Gamma "ctx"$, $Epsilon[Delta] tack sigma_1 equiv sigma_2 : Gamma$ and $Epsilon[Gamma] tack e_1 equiv e_2 : t$, then $Epsilon[Delta] tack e_1 [sigma_1] equiv e_2 [sigma_2] : t[sigma_1]$.
]

#proof[
  By induction on the derivation of $Epsilon tack Gamma "ctx"$, using substitution and #smallcaps[$forall$-$beta$].
]

#theorem("Definitional inversion")[
  Suppose $tack Epsilon "env"$ and $Epsilon tack Gamma "ctx"$.
  + (Injectivity of sorts) If $Epsilon[Gamma] tack Sort(l_1) equiv Sort(l_2) "type"$, then $l_1 = l_2$.
  + (Injectivity of $forall$) If $Epsilon[Gamma] tack forallE(x, t_1, t'_1) equiv forallE(x, t_2, t'_2) "type"$, then $Epsilon[Gamma] tack t_1 equiv t_2 "type"$ and $Epsilon[Gamma, x : t_1] tack t'_1 equiv t'_2 "type"$.
  + (Injectivity of inductive types) If $Epsilon[Gamma] tack Ind(s, overline(l)_1, overline(p)_1, overline(i)_1) equiv Ind(s, overline(l)_2, overline(p)_2, overline(i)_2) : Sort(l_I {overline(l)_1 slash overline(u)})$, then $overline(l)_1 = overline(l)_2$, and each $p_(1,k) equiv p_(2,k)$ and each $i_(1,k) equiv i_(2,k)$ holds in $Epsilon[Gamma]$ at some type.
  + (Injectivity of quotient types) If $Epsilon[Gamma] tack quot(l_1, alpha_1, r_1) equiv quot(l_2, alpha_2, r_2) "type"$, then $l_1 = l_2$, $Epsilon[Gamma] tack alpha_1 equiv alpha_2 "type"$ and $Epsilon[Gamma] tack r_1 equiv r_2 : alpha_1 -> alpha_1 -> Prop$.
  + (No-confusion) Types headed by different type formers, and inductive types of different blocks or sorts, are not type-equal.
]

#proof[
  Adequacy of the domain model!
]

#corollary("Equational consistency")[
  Not all definitional equalities hold.
]

#proof[
  By no-confusion, e.g. $Prop equiv.not Prop -> Prop$.
]

#theorem("Uniqueness of typing")[
  Suppose $tack Epsilon "env"$ and $Epsilon tack Gamma "ctx"$. If $Epsilon[Gamma] tack e : t_1$ and $Epsilon[Gamma] tack e : t_2$, then $Epsilon[Gamma] tack t_1 equiv t_2 "type"$.
]

#proof[
  Assume $Epsilon[Gamma] tack e : t_1$ and generalise to $Epsilon[Gamma] tack e_1 equiv e_2 : t$, then every type of $e_1$ or of $e_2$ is type-equal to $t$, by induction on the typing derivation of $Epsilon[Gamma] tack e_1 equiv e_2 : t$. Use syntactic inversion and the injectivity clauses of definitional inversion.
]

#theorem("Uniqueness of sorts")[
  Suppose $tack Epsilon "env"$ and $Epsilon tack Gamma "ctx"$. If $Epsilon[Gamma] tack t_1 equiv t_2 "type"$, then $Epsilon[Gamma] tack t_1 equiv t_2 : Sort(l)$ for some $l$.
]

#proof[
  By induction on the derivation of $Epsilon[Gamma] tack t_1 equiv t_2 "type"$, recall it is defined as the transitive closure of $Epsilon[Gamma] tack t_1 equiv t_2 : Sort(u)$. In the transitive case, the middle type has two sorts $Sort(l_1)$ and $Sort(l_2)$, so apply uniqueness of typing and injectivity of sorts to get $l_1 = l_2$.
]

#judgement([weak-head reduction], $Epsilon tack e_1 arrow.r.squiggly e_2$)[
  Elimination frames:
  $
    K in "Frame" ::= app(square, a) | recr(I, s, overline(l), v, overline(p), overline(mu), overline(overline(m)), overline(i), square) | quotLift(l_1, l_2, alpha, r, beta, f, h, square) | quotInd(l, alpha, r, beta, f, square)
  $

  #rules(
    rule(name: [frame], $Epsilon tack e_1 arrow.r.squiggly e_2$, $Epsilon tack K[e_1] arrow.r.squiggly K[e_2]$),
    rule(name: [$beta$], $Epsilon tack app((lam(x, t, e)), a) arrow.r.squiggly e[a slash x]$),
    rule(name: [$zeta$], $Epsilon tack letE(x, t, v, e) arrow.r.squiggly e[v slash x]$),
    rule(
      name: [$delta$],
      $(def c.{overline(u)} : t := e) in Epsilon$,
      $Epsilon tack c.{overline(l)} arrow.r.squiggly e{overline(l) slash overline(u)}$,
    ),
    rule(
      name: [$iota$],
      $Epsilon tack recr(I, s, overline(l)_1, v, overline(p)_1, overline(mu), overline(overline(m)), overline(i), ctor(I, s, c, overline(l)_2, overline(p)_2, overline(a), overline(r))) arrow.r.squiggly "rhs"^(s,c)$,
    ),
    rule(
      name: [quot-$iota$],
      $Epsilon tack quotLift(l_1, l_2, alpha, r, beta, f, h, quotMk(l'_1, alpha', r', a)) arrow.r.squiggly app(f, a)$,
    ),
    rule(
      name: [quot-ind-$iota$],
      $Epsilon tack quotInd(l, alpha, r, beta, f, quotMk(l', alpha', r', a)) arrow.r.squiggly app(f, a)$,
    ),
  )
  where $"rhs"^(s,c)$ is taken at the levels $overline(l)_1$ and parameters $overline(p)_1$ of the recursor. Write $Epsilon tack e_1 scripts(arrow.r.squiggly)^* e_2$ for the reflexive transitive closure.
]

#theorem("Subject reduction")[
  Suppose $tack Epsilon "env"$ and $Epsilon tack Gamma "ctx"$. If $Epsilon[Gamma] tack e_1 : t$ and $Epsilon tack e_1 scripts(arrow.r.squiggly)^* e_2$, then $Epsilon[Gamma] tack e_1 equiv e_2 : t$.
]

#proof[
  By induction on the reduction, it suffices to treat one step, by induction on its derivation.
  - #smallcaps[frame]: congruence
  - $beta$: injectivity of $forall$
  - $iota$: injectivity of inductive types
]

#proposition("K-like reduction")[
  Suppose $tack Epsilon "env"$ and $Epsilon tack Gamma "ctx"$. If $Epsilon[Gamma] tack Ind(s, overline(l), overline(p), overline(i)) : Prop$, $Epsilon[Gamma] tack x : Ind(s, overline(l), overline(p), overline(i))$, $Epsilon[Gamma] tack ctor(I, s, c, overline(l), overline(p), overline(a), overline(r)) : Ind(s, overline(l), overline(p), overline(i))$ and $Epsilon[Gamma] tack recr(I, s, overline(l), v, overline(p), overline(mu), overline(overline(m)), overline(i), x) : t$, then
  $
    Epsilon[Gamma] tack recr(I, s, overline(l), v, overline(p), overline(mu), overline(overline(m)), overline(i), x) equiv "rhs"^(s,c) : t.
  $
]

#proof[
  By #smallcaps[pf-irrel], $x equiv ctor(I, s, c, overline(l), overline(p), overline(a), overline(r))$, so by #smallcaps[ind-elim] the recursor on $x$ is equal to the recursor on the constructor, which is equal to $"rhs"^(s,c)$ by subject reduction for $iota$.
]

#proposition("Unit-like eta")[
  Suppose $tack Epsilon "env"$ and $Epsilon tack Gamma "ctx"$, $I in Epsilon$, $tack I_"ctor"^(s,c) "struct"$ and $I_"ctor"^(s,c)$ has no fields. If $Epsilon[Gamma] tack overline(p) : Gamma_"param"$, $Epsilon[Gamma] tack x_1 : Ind(s, overline(l), overline(p), ())$ and $Epsilon[Gamma] tack x_2 : Ind(s, overline(l), overline(p), ())$, then $Epsilon[Gamma] tack x_1 equiv x_2 : Ind(s, overline(l), overline(p), ())$.
]

#proof[
  Since the constructor has no fields, $eta(x_1)$ and $eta(x_2)$ are both $ctor(I, s, c, overline(l), overline(p), (), ())$, which is well-typed by well-formedness of $I$. By #smallcaps[struct-$eta$], $x_1 equiv eta(x_1) = eta(x_2) equiv x_2$.
]

= Soundness of the checker

= Domain model

= Gluing model

= Consistency
