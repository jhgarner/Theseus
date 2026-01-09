# Theseus

> This library is still in progress and not ready to be shared widely. If you've
> stumbled upon this now, take a look but know that it's still a bit of a mess.

Welcome to the hub for Theseus, an effect system library for Haskell. Theseus is
an effect system that supports the full suite of algebraic effects (including
Coroutine) and many higher order effects. It accomplishes this while also
ensuring that semantics do not change when effects are reordered.

We'll explore how, much like the Ship of Theseus, programs can be deconstructed
and rebuilt in many ways without changing their underlying identity.

## Guides

Theseus contains several annotated source files transformed into docs using
Docco. Those are the best place to learn more about Theseus.

For getting started, there are a couple good places:

* The tutorial is the best starting place. If you're new to effect systems, it
  should bring you up to speed with a couple of examples. If you're only new to
  Theseus, it'll cover some of what makes Theseus unique.
* The File example showcases Theseus' main feature. If you're experience with
  effect systems and want to know what makes Theseus special, look there.

The builtin effects are useful to walk through as well since they the range of
Theseus' complexity.

* The Reader implementation covers a simple higher order effect.
* The State implementation covers a simple first order effect that changes the
  return type.
* The Writer implementation is a higher order effect that also changes the
  return type.
* The Error implementation introduces Theseus' control flow manipulation
  features.
* The Coroutine effect gives another example of unique control flow.
* The Choice implementation shows the most complicated control flow.

Finally there's the inner workings. These might be helpful while you're looking
into the more complicated effects.

* The Eff definition explains how it's all defined.
* The interpreters explain how it can be used.

## Shoutouts

There are some other amazing effect system libraries in Haskell exploring this
space. Brief summaries follow, although it's worth finding them on Github and
reading their docs as well.

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
