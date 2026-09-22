# metalean

Verified typechecker for idealised type theory of Lean.

The checker is positively sound (if it accepts, then it is derivable in the theory), partial (it may not terminate on some inputs), but not negatively sound (if it rejects, it does not necessarily imply that it is underivable).

We support mutual inductive types (but not nested inductive types), η laws for structures, and universe polymorphism including the dreaded `Sort u`.

## Metatheoretic results

### Soundness

As in [DIWM (2026)](https://arxiv.org/pdf/2607.13662), we use semantics in the language of domain theory to avoid talking about normal forms, since Lean is non-normalising. We then internalise the domains into a natural model of the type theory. This gives adequacy of the model without appealing to a logical relation explicitly, but "categorifying" the logical relation (or so I hear).

Consequences include the elusive "definitional inversion", consisting of injectivity of type constructors (on the diagonal) and no-confusion (on the off-diagonal), uniqueness of typing, uniqueness of sorts, subject reduction.

### Consistency

As in [Carneiro (2019)](https://github.com/digama0/lean-type-theory/releases), we take a naive (obvious) translation into ZFC Set theory with an axiom assuming the nth inaccessible cardinal exists for all ordinal n below omega, thus constructing Grothendieck universes.
Furthermore we show that the type theoretic notions of propositional extensionality, quotient types, and the axiom of choice, have a model.
From soundness of the model, we obtain consistency. The precise statement of consistency, defines a barebones environment containing the bare minimum of (`Eq`, `Iff`, `Nonempty`, `propext`, `Quot.sound`, `Classical.choice`). Assuming that no further additions to the environment are _axioms_, we have that `∀ P : Prop, P` is uninhabited.

## Object language

Terms [(Expr.lean)](Metalean/Syntax/Expr.lean)

`Expr (ζ : Sigs) (ℓ : Nat) (n : Nat)` seems like a silly type signature for expressions.

- `ζ : Sigs` is a snoc-list of the "shape" of the environment. It describes, in what ways can a term legally refer to something in the environment. For example, you can say you want "the 7th entry in the environment, which I assume to be an inductive type, and in that inductive type, I want the second sort (out of a mutual block containing 2 inductives), and the third constructor, applied to some parameters, some fields, and some recursive fields", and `Expr.ctor` can do this, and it will be a _total_ operation.
- `ℓ : Nat` represents the number of universe variables.
- `n : Nat` represents the number of binders in the local context.

Typing [(Defs.lean)](Metalean/Typing/Defs.lean)

- We include transitivity as a rule.
- "Unit-like" η is admissible from regular η for structures.
- "K-like" reduction (for subsingleton inductive propositions) is admissible from proof irrelevance.
- We include quotient lifting.
- Quotient induction is admissible from proof irrelevance.

## Checkers

- There is a "logical" checker [(Checker)](Metalean/Checker/Infer.lean), which is EXTREMELY slow. This is because, it uses the exact same `Expr ζ ℓ n` type as the metatheory which, while nice to prove things about, contains atrocities such as `Fin k → Expr ζ ℓ n` for k-tuples, does not support nat/str literals, and type indices that are not erased at runtime.

- For this reason there is a "fast" (still slow!) checker [(Checker)](Metalean/FastChecker/Infer.lean) that attempts to mimic the official Lean kernel. It uses a raw `FExpr` type that is related to `Expr ζ ℓ n` extrinsically. It supports nat/str literals, and the corresponding accelerated operations. It uses some `unsafe`/`implemented_by` for performance reasons, which you just have to trust.

## Differences from Lean

- No nested inductives (yet).
- No unsafe or partial definitions.
- Inductive/quotient type formers, constructors and recursors are primitive term formers. This results in subtly supporting function η in more cases than what official Lean checks for, since when these are partially applied, the translator inserts function bindings.
- Since recursive fields in an inductive type constructor cannot be depended on in a meaningful way (since it would violate positivity), we consider all recursive fields to be effectively declared as coming last. This is justifiable, since we are merely weakening the context in which they are available. It means that the frontend must permute the fields sometimes, and remember that it permuted them.
