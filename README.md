# Theseus

Welcome to the hub for Theseus, an effect system library for Haskell. Theseus is
an effect system that supports algebraic effects (including Coroutine), many
higher order effects, and is designed so that semantics do not change when
effects are reordered.

We'll explore how, much like the Ship of Theseus, programs can be deconstructed
and rebuilt without changing what they are.

## Guides

Theseus contains several annotated source files transformed into docs using
Docco. Those are the best place to learn more about Theseus.

For getting started, there are a couple good places:

* [The tutorial](https://jhgarner.github.io/Theseus/test/Terminal.html) is the
  best starting place. If you're new to effect systems, it should bring you up
  to speed with a couple of examples. If you're only new to Theseus, it'll cover
  some of what makes Theseus unique.
* [The File example](https://jhgarner.github.io/Theseus/test/FileExample.html)
  showcases Theseus' main feature. If you're experienced with effect systems and
  want to know what makes Theseus special, look there.

The builtin effects are useful to walk through as well since they cover the
range of Theseus' complexity.

* [The Reader implementation](https://jhgarner.github.io/Theseus/src/Theseus/Effect/Reader.html) covers a simple higher order effect.
* [The State implementation](https://jhgarner.github.io/Theseus/src/Theseus/Effect/State.html) covers a simple first order effect that changes the
  return type.
* [The Writer implementation](https://jhgarner.github.io/Theseus/src/Theseus/Effect/Writer.html) is a higher order effect that also changes the
  return type and depends on a finalizer.
* [The Error implementation](https://jhgarner.github.io/Theseus/src/Theseus/Effect/Error.html) introduces Theseus' control flow manipulation
  features.
* [The Coroutine effect](https://jhgarner.github.io/Theseus/src/Theseus/Effect/Coroutine.html) gives another example of unique control flow.
* [The Choice implementation](https://jhgarner.github.io/Theseus/src/Theseus/Effect/Choice.html) shows the most complicated control flow.

Finally there are the inner workings. These might be helpful while you're
looking into the more complicated effects.

* [The Eff definition](https://jhgarner.github.io/Theseus/src/Theseus/EffType.html) explains how it's all defined.
* [The interpreters](https://jhgarner.github.io/Theseus/src/Theseus/Interpreters.html) show how consuming works.

## Shoutouts

There are some other amazing effect system libraries in Haskell exploring this
space. A non-exhaustive list of ones I'm familiar with are:

* Fused-effects and Polysemy use a freer monad and Weave abstraction. They
  support a large number of higher order effects, but sacrifice some of the
  richer algebraic effects (like Coroutine) in the process.
* Eff approaches it with delimited continuations. Eff finds great success
  supporting the algebraic effects, but runs into more problems with the higher
  order effects.
* Bluefin, Effectful, and Cleff use a ReaderT IO based approach. They sacrifice
  even more of the algebraic effects (NonDet) for speed and ecosystem
  interoperability.
* Heftia's approach supports the full gamut of algebraic and higher order
  effects. In exchange for all that support, it limits when richer algebraic
  effects can run.

Theseus, compared to those, is most similar to the free/freer effect systems. It
changes some of the algebraic effect semantics (the biggest being that Choice is
more breadth first than depth first), but in exchange has higher order effects
and algebraic effects that play well with each other.
