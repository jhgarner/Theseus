# Notes

## Higher Order Semantics

A higher order effect has two "scopes" it exists in. There's the handler scope
and the send scope. Things that are safe to do include:

* Dispatch an effect you know is in the lower scope to the lower scope
* Run an effect you received in the higher scope

Basically there are two options:

1. runLocked -- Runs an action using the handlers that were in scope when the
   handler was added
1. runOpen -- Runs an action using the handlers that were in scope when the
   action was sent

## Tracking affinity

Eff contains an `open` stack of effects. If this is nonempty, the current code
might run multiple times.

```haskell
interpret
  :: (eff (Eff open es) ~> Eff open es)
  -> Eff open (eff:es) a
  -> Eff open es a

finalizingInterpret
  :: (eff (Eff '[] es) ~> Eff '[] es)
  -> Eff '[] (eff:es) a
  -> (a -> Eff '[] es)
  -> Eff '[] es a

finalizingInterpret
  :: (eff (Eff '[] es) ~> Eff '[] es)
  -> Eff '[] (eff:es) a
  -> (a -> Eff '[] es)
  -> Eff '[] es a
```
