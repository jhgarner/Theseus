# Theseus

This library is still in progress and not ready to be shared widely. If you've
stumbled upon this now, take a look but know that it's still a bit of a mess.

> This document is not (yet) an effect system tutorial. It assumes familiarity
> with other effect system libraries and to some extent their implementations.

Theseus is an effect system which supports the full suite of algebraic effects
(including Coroutine) and a useful subset of higher order effects. It
accomplishes this while also ensuring that semantics do not change when effects
are reordered.

We'll explore how, much like the Ship of Theseus, programs can be deconstructed
and rebuilt without losing their identity.

## Goals

There appear to be three competing goals in effect system design: supporting
rich control flow effects, supporting higher order effects, and having semantics
that are locally definable. Let's break them down and see how Theseus tries to
make these work together.

### Rich Control Flow Effects

Theseus supports the full power of continuations without relying on IO. There
are some restrictions though if you want to use the Coroutine effect. It will
not compose at compile time with higher order effects which try to thread
non-trivial state through the continuation. So far the only effect handler that
applies to is `runCatchNoRecovery`. The issue is that `runCatchNoRecovery` needs
to track whether the continuation should abort based on the result of higher
order computations. At the same time, `runCoroutine` requires that any threaded
state be `Distributive` which `Maybe` (`runCatchNoRecovery`'s state) is not.
This means that composing them in the wrong order leads to a compiler error.

Note that this restriction specifically applies to a fancy kind of threaded
state. It does not apply to the `State` effect (or most other higher order
effects including normal `Catch` handlers). It also doesn't prevent you from
using `runCatchNoRecovery` and `runCoroutine` together. You just have to make
sure `runCatchNoRecovery` is executed before `runCoroutine` is executed.

The system which backs this threaded state is pretty flexible and is tracked by
the `ef` variable on `Eff`. The `ef` name stands for "extra facts" because it
marks the extra constraints that other parts of the codebase can assume to be
true.

### Higher Order Effects

This is the part where Theseus budges the most. Theseus is designed to support a
useful subset of higher order effects (such as Catch, Local, and Writer). It
does not support all possible higher order effects though. For example, the
following would be impossible to define in Theseus.

```haskell
data Defer a :: Effect where
  defer :: m a -> Defer m a ()

runDefer :: Eff (Defer a : es) b -> Eff es a
runDefer = error "Can't implement this!"
```

The general rule is that all higher order effects must be run while computing
the value to continue with. Once higher order effects begin running, they cannot
be stopped until the entire continuation completes. There is a threaded state
which you can use to pass computations through the continuation to the other
side.

### Locally Definable Semantics

Where spooky action at a distance is possible, we should try to minimize or
localize it. Effect ordering is the kind of spooky action at a distance that we
should try to avoid as there's no way to really guess which ordering will be
used.

Theseus adopts the global state semantics as that's the most intuitive (if you
told a Java programmer that mutable variables would be reset after an exception
was thrown, they'd look at you funny). Transactional/local semantics can be
recovered using interpose or similar tricks to define the local boundaries. This
gives everyone a consistent and reasonable default along with the ability to
override that default locally.

Theseus also treats effects as stronger abstraction boundaries than normal
function calls. By default effects are only influenced by effects that are in
scope when the handler is run. If they want to be influenced by effects that are
in scope when the effect is used, they must declare that as part of the effect's
signature. This makes it easy to reason about which handlers will be called. The
difference between these scopes is encoded in `es` vs `esSend` in the `Handler`
type.

## Downsides

### Efficiency

No attempt has been made to make Theseus fast, both in terms of constant factors
and algorithmic complexity. There's no reason Theseus couldn't be made faster
though. For example, the open union datatype could be replaced with one of many
optimized alternatives. Slow things were used during this prototyping phase
because they're easier to reason about. In a previous version I played fast and
loose with unsafeCoerce and primops which made everything harder. At this point
I would feel more comfortable swapping in faster (possibly unsafe) data
structures, but that hasn't been done yet.

### Outdated Handlers

If the program yields while running a higher order effect, any running handlers
will be captured inside the continuation even if you try to swap out the
implementations. After the handler finishes running, the new one will be used.
This is surprising, but it shouldn't be unsound. If you're writing an effect
handler, there's a chance your handler will be called long after you thought
your handler finished running.

You have to be careful about how you write your higher order effects if you want
to make sure that the most up to date behavior is always used. Figuring out
which patterns work well and making those easy is still needed.
