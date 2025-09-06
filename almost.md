# Almost

I'm not really satisfied with how Choice works, and I think there's a better way
to handle it.

## Problem

Choice doesn't compose well with things like State or catching because the
behavior can change when the effect ordering changes. To get around this,
Theseus requires that all effects happen after Choice is handled. This is more
limiting than it has to be though. For example, there should be no problem with
running a Reader effect before running the Choice (TODO I think so?).

## Threading

One of the parameters to `handleRaw` is a threading function. It says that you
need to convert a `wrap (g a)` into a `g (wrap a)`. The `wrap` parameter is some
Functor that the handler picks to modify the thing that's returned. The `g`
parameter is the control flow that some other handler is currently using. If `g`
is `Identity`, it means that the control flow is extremely simple and linear. If
`g` is `Maybe`, it means that control is affine and might stop unexpectedly. If
`g` is `Const`, it means control will not continue. The threading function says
how we can distribute our result through the branches of the control flow.

Given that `g` represents control flow, it seems like `Choice` should be able to
use it. In that case, `Choice` could use an arbitrary `Representable` functor
for its control flow. The standard formulation for `Choice` would use something
like `data Both a = Both a a` and a `Rep` of `Bool`. We could implement `Choice`
for any arbitrary `Rep` though!

This formulation would make the limitations around `Choice` and `State` obvious.
The output of `State`, a `newtype StateResult s a = StateResult s a`, cannot
duplicate itself (it needs to be used in an affine way). This implies that `g`
must only have 0 or 1 `wrap a`s inside of it. `Maybe` and `Identity` are fine,
but `Both` is not. We could define an `AffineFunctor` similar to the linear
control functor defined in `linear-base`, and some kind of `Pointed` class.
Those classes can be used as `ef` on `Eff` in the `State` handler. Now it's a
type error to use `State` and `Choice` in the wrong order.

But this doesn't work...

If you try to fill in `Both` for `g`, the Monad implementation for `Eff` will
use `traverse` to duplicate the computations across both of the branches.
Although this sounds right, it causes the `continue` parameter to the `Choice`
handler to contain not just the rest of the current branch, but the entire
second branch as well. This is clearly wrong because the `Choose` needs to be
scoped to just its current branch. I'm not sure how to make it work such that
you can detect which branch you're running on. I tried one thing with Yield in
this commit, but it's complicated and still broken.

It's unfortunately not clear how this interacts with the `Coroutine` effect.
Saying that `g` represents the control flow only really works if you call the
continuation linearly. Otherwise you can choose to drop or duplicate things
arbitrarily without restriction. Maybe the point is that anything which uses the
continuation non-linearly must be handled first so that we guarantee consistent
semantics, but anything which uses `g` doesn't have that restriction? Is there
some `g` which can represent `Coroutine`'s control flow? Some kind of lazy
stream maybe, but that's not `Traversable` which means `Eff` won't be a `Monad`.

If it doesn't work, why bother writing all this up? There seems to be something
really interesting about how `StateResult`, affine Functors, and a
`Representable` based `Choice` effect all interact.
