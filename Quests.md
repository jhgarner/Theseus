# Quests

Theseus sets out on a main quest with two side quests. The three are largely
independent, but that's hard to see if you're looking at the code and the
haddocks. This article explains Theseus' design by splitting it up between these
three quests.

## Main Quest - Higher Order and First Order Effects Coexisting

Theseus' main quest is to explore how higher order effects can compose with rich
algebraic effects.

### Other Libraries

I'm aware of other libraries also exploring this space.

* Fused-effects and Polysemy approach it using the Weave abstraction. They
support a large number of higher order effects, but sacrifice some of the richer
algebraic effects (like Coroutine) in the process.
* Eff approaches it with delimited continuations. Eff finds great success
supporting the algebraic effects, but runs into more problems with the higher
order effects.
* Bluefin, Effectful, and Cleff use a ReaderT IO based approach. They sacrifice
even more of the algebraic effects (NonDet) for speed and ecosystem
interoperability.
* Heftia's approach supports the full gamut of algebraic and higher order
effects. In exchange for all that support, it limits when richer algebraic
effects can run.

Theseus pulls a little from many of these approaches. It finds a design which
supports rich algebraic effects and a restricted subset of higher order effects.
Because that restricted subset includes the popular and useful effects, that's
not a big deal. Most "normal" handlers can even avoid the restrictions around
handler order.

### Theseus' Freer

Theseus strikes out on its quest armed with the following data type. You can
refer back to this while reading its description below.

```haskell
type Freer :: ExtraFacts -> [Effect] -> Type -> Type
data Freer ef es a
  = Pure a
  | forall (efSend :: ExtraFacts) (esSend :: [Effect]) x. Impure
      (Union es (Eff efSend esSend) x)
      (forall g. (ef g, Traversable g, Applicative g) => Eff efSend esSend (g x) -> Eff ef es (g a))
```

The Impure case is the interesting one. It's heavily inspired by Heftia's data
type.

#### Storing the Effect

The first parameter to Impure is the effect that needs to be run. This is a
single `Ask`, `Put x`, `Catch ma mb`, `Yield z`, etc. Once stored, it will not
change. The `ef` and `es` variables on any higher order operations at the time
it was sent will be preserved as `efSend` and `esSend`.

#### Storing the Continuation

The second parameter is the continuation (for now we'll ignore `g`). It contains
the rest of the program. The continuation accepts an action that can fill in for
the original effect, then it returns whatever the rest of the program would
return. This is where we convert from the environment where the effect was used
into the environment where the effect is being handled. Because `esSend` is
existential in `Freer`, the only thing a handler can do with a higher order
operation is pass it on to the rest of the program.

This gives us a version of Scoped Effects without having to worry about higher
order functors. An important difference from the usual definition of Scoped
Effects though is that the environment is existential instead of the return
type.

#### Beyond Scoped Effects

The `g` variable is how the handler gets back information about the higher order
operations that ran. The handler can pick any `g` it'd like as long as it's
`Traversable` and `Applicative`. The most common `g` is `Identity` which signals
that a handler does not need to know anything about what the higher order
operations returned. `Maybe` is used by one of the `Catch` handlers to signal
that an unrecoverable `throw` was called. Although I don't have any examples
right now, `Const` could be used to run a higher order operation without running
the rest of the program.

The `ef` variable tracks any extra constraints that `g` will have
to follow (or looking at it from the opposite perspective, any extra facts about
`g` that other handlers can assume). Given an `Eff ef es a`, it's possible to
restrict `ef` to require more constraints, but it's not possible to weaken it.
By restricting `g` to `Distributive`, the `Coroutine` effect can make sure the
continuation it needs to return won't get stuck inside `g`. Because `ef` can
only be changed in one direction, the order of some handlers is restricted. Most
handlers (including ones for `State`, `NonDet`, `Reader`, and `Catch`) will use
`Identity` for `g`. `Identity` implements so many type classes that those
handlers can be rearranged before or after a handler for `Coroutine` without
issue even if they're higher order. Handlers that want to use `Maybe` or `Const`
must be run before the handler for `Coroutine` because those types are not
`Distributive`.

Side note: I find it really easy to get caught up on the word "before" when
talking about when handlers run. It's tempting to interpret before to mean that
`runX` is before `runY` in `runX . runY`. In this context though, before means
that `runY` is run before `runX` because all the `Y` effects have to be handled
before we can handle `X` effects.

Overall, Theseus is well equipped for its quest to explore effect systems thanks
to this Freer datatype.

## Side Quest - Order Independent Effects

As a side quest, Theseus tries to tame the effect system semantics zoo. This is
a side quest because it's orthogonal to the main quest and doesn't really have
anything to do with the underlying `Freer` datatype. Instead it has more to do
with how we define the effects.

In most effect systems, reordering the effect handlers can cause local behavior
to change wildly. The Eff project points out how confusing this can be, although
it doesn't completely get rid of the ordering. Theseus takes a stronger stance:
reordering effect handlers must not change the local behavior of code.

The `Catch` and `State` effects in Theseus follow this rule. `State` will never
roll back when an exception is thrown regardless of how the handlers are
ordered. More controversially, the `Choice` effect also follows this rule. It
must be the topmost effect in the stack when `Choose` is used. This guarantees
global state semantics. If `Choice` can't be the topmost effect in the stack,
combinators are provided so that global state semantics are preserved. This
solves the handler ordering problem by making it a type error if the correct
order is not used for `Choice`. While it's possible to define effects and
handlers that are order dependent, those should be considered buggy.

It's always possible to restore the lost behavior locally.

* The body of a catch block could intercept interactions with a specific `State`
effect and defer writing them to the more global state until after the block
succeeds.
* Before running one of the branches of a `Choice`, you could save the state
somewhere and restore it before running the second branch.

These kind of options are good because they encourage encapsulation. A block of
code using `Catch` or `Choice` can decide how state works locally without being
affected by spooky action at a distance.

`Coroutine` is an interesting case that I'm divided on. Theseus is named for
`Coroutine`'s ability to arbitrarily change how effects are interpreted. Across
a call to `yield`, behavior might change drastically. For example, `ask` might
suddenly return a different value. Although this wild behavior could be tamed by
requiring that `Coroutine` be the top of the stack, that's probably too
restrictive. For now it'll stay unrestricted, but I'm interested in finding ways
to make it more principled.

## Side Quest - Handler Abstraction Boundaries

This side quest is more tightly coupled with the main quest. In the name of
composability, calls to effects introduce strong abstraction boundaries.
Consider the following effect stack containing X, Y, and a couple State effects:
`[X, State Int, Y, State Int]`. The leftmost/topmost State is currently 7 and
the rightmost state is currently 34. If you ran `get` within this effect stack,
you'd get 7 because that's the first `State Int` that's encountered on the
stack. Effects are masked by any equivalent effects above them on the stack.

Within the handler for `X` calls to `get` will also return 7. What would you
expect to happen when you call `get` within a handler for `Y`? That depends on
whether you're sending `Get` to `es` or `esSend` in the handler. Using `es`,
you'll get 34 because `es` only contains effects that are lower than `Y` in the
stack. If you use `esSend`, you'll get 7 because `esSend` contains the full
effect stack when the effect was sent.

Handlers get to decide when the effects they depend on can be overridden. If an
effect can be overridden, it must be marked publicly by the effect's signature.
For example, if the `Y` effect has an operation `DoY` it must be defined as the
following in order for `State Int` to be overridable.

```haskell
data Y :: Effect where
  DoY :: State Int `Member` es => Y (Eff ef es) ()
```

In contrast, no handler for the following definition would be allowed to make
the state overridable.

```haskell
data Y :: Effect where
  DoY :: Y m ()
```

This means the users of effects must be told whether they might override
something. As a more concrete example, a network effect which forces users of
the effect to handle failures would be defined as the following.

```haskell
data Network :: Effect where
  GetRequest :: Throw NetworkError `Member` es => Url -> Network (Eff ef es) ByteString
  PostRequest :: Throw NetworkError `Member` es => Url -> Body -> Network (Eff ef es) ByteString
```

Hopefully it's clear how separating the effect environments makes the
interactions between effects more consistent and powerful.
