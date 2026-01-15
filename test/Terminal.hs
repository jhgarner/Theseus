module Terminal where

import Control.Monad
import Control.Monad.IO.Class
import System.IO (IOMode (ReadWriteMode), hClose, hGetLine, hPutStrLn, openFile)
import Test.Hspec (SpecWith, describe, it)
import Test.Hspec qualified as Test
import Theseus.Eff
import Theseus.Effect.IO
import Theseus.Effect.Input
import Theseus.Effect.Output
import Theseus.Effect.State

-- # Tutorial

-- This module is a tutorial for Theseus. If you're familiar with other effect
-- systems, it should all be pretty similar. If not, hopefully it walks you
-- through the basics. Regardless of your experience level, reach out if you
-- have any questions!
--
-- When you use an effect system library, you'll end up with a pyramid of
-- effects. At the bottom of the pyramid are low level generic effects. Those
-- are used to implement more specific higher level effects. Instead of only
-- composing functions, you can also compose effects. Since effects
-- can be easily swapped out, you can mock any part of your effect stack. This
-- makes it easy to write anything ranging from unit tests to integration
-- tests. In general, functions should have a very small number of effects
-- associated with them. If a function's signature begins to grow unwieldy, it
-- probably means you need to introduce a new effect to abstract away
-- something.

-- ## Affecting the World

-- Let's jump into how you use Theseus. Our goal is to implement
-- a Terminal effect that interacts with stdin and stdout. We'll also include
-- a test implementation and a test program that we can verify. This is
-- a common example across effect system libraries because it matches the
-- common case. Most effects will be like the Terminal effect: domain specific
-- and fairly simple. In general you should never be afraid of introducing new
-- effects.

-- ### Creating Effects

-- An effect consists of a bundle of functions. We define that bundle using
-- a GADT. This can feel a bit like an abuse of notation, but GADTs are
-- a convenient way of representing them. Each constructor of a GADT represents
-- an operation, and the syntax for defining a constructor is remarkably close
-- to that of a function signature. You can even write polymorphic functions
-- with constraints as GADT constructors. The illusion breaks down a bit when
-- you see the return type of the GADT constructor. The return type will
-- consist of the effect's name followed by a mysterious `m` parameter (which
-- we'll explain later in the tutorial) followed by the actual return type of
-- the function. Anyway, when you see a GADT of kind `Effect`, look past the
-- GADT and think about the bundle of functions.
data Terminal :: Effect where
  WriteLine :: String -> Terminal m ()
  ReadLine :: Terminal m String

-- Now for some functions that send our effects. Most effect systems use
-- template haskell to generate these. Theseus doesn't have that yet. They're
-- boring boilerplate, but we'll use them to show a couple new concepts. Effect
-- systems separate sending effects from interpreting them. The code that sends
-- effects says nothing about how the receiver will interpret them. This is
-- what makes effect systems so useful for testing. Effects sent for a database
-- call could be interpreted using a real connection, using a mocked database,
-- or anything else. One block of code can be interpreted in any number of
-- ways.

-- A few things are introduced in this line. `Eff` is the Monad that our effect
-- system runs in. The `ef` parameter we'll ignore for now. The `es` parameter
-- is a type level list of effects. The `es` parameter will change as the
-- program runs and effects are handled and introduced. Within one "level" of
-- code (think all the actions within the same do block) it will remain the
-- same. You have to introduce new "levels" to change it. We'll see examples of
-- that when we get to interpreting effects. By making `es` generic, we're
-- saying that (almost) any list of effects will work. The `Member` constraint
-- limits the list to those that contain `Terminal`. We can only `send` effects
-- to `Eff` if they're part of the effect stack. All effects that are in the
-- stack are effects that `Eff` can handle.
--
-- It's possible for there to be multiple instances of the same effect in the
-- stack. That's fine! The `Member` constraint will find the topmost one.
writeLine :: Terminal `Member` es => String -> Eff ef es ()
writeLine line = send $ WriteLine line

readLine :: Terminal `Member` es => Eff ef es String
readLine = send ReadLine

-- Now let's look at how we can use our effects. We'll implement a program that
-- reads input from the user and echos what they provided 3 times.

thrice :: Terminal `Member` es => Eff ef es ()
thrice = do
  lineToEcho <- readLine
  writeLine lineToEcho
  writeLine lineToEcho
  writeLine lineToEcho

-- Hopefully that's not too hard to follow. Except for the type signature, it
-- should look nearly identical to how you'd write it normally. This is code
-- that sends effects; it says nothing about the interpretation. That means we
-- can reuse it in many ways.

-- ### Interpreting Effects

-- Let's create our first interpretation doing what you'd expect from
-- a terminal effect: reading and writing to stdin and stdout.

-- Here we see our first use of `ef`. Honestly, `ef` is kind of messy The `ef`
-- variable is a Constraint on how interpreters are allowed to modify the
-- effectful computation's return type. Technical all interpreters wrap the
-- computation in some Functor. Most of the time that's `Identity`, so the
-- `interpret` function handles the wrapping and unwrapping for you. By adding
-- `ef Identity` as a constraint, we're saying that `Identity` must be
-- a wrapper that all other interpreters know how to handle. Once again, we
-- don't really care much about `ef` most of the time. Usually effect
-- interpreters support all wrappers and use the `Identity` wrapper themselves.
-- We only need this because a handful of uncommon (but powerful) interpreters
-- require it. If you're not writing one of those effects, just add `ef` to
-- your interpreter's type signature with whatever value the compiler requires.
--
-- The other constraint we have is for the `EIO` effect. EIO says that we can
-- lift arbitrary IO operations into `Eff`. When `EIO` is a member of the
-- effect stack, `Eff` implements `MonadIO`.
runTerminal :: (ef Identity, EIO `Member` es) => Eff ef (Terminal : es) a -> Eff ef es a
runTerminal = interpret_ \case
  WriteLine line -> liftIO $ putStrLn line
  ReadLine -> liftIO getLine

-- Now we have everything we need to turn our `thrice` function into something
-- Haskell can actually run. The `runEffIO` function turns an effect stack that
-- only contains the `EIO` effect into an IO operation.
thriceIO :: IO ()
thriceIO = runEffIO $ runTerminal thrice

-- Great! Now we have one interpretation we can use in production, but we'd
-- really like to have a test interpretation as well which doesn't interact
-- with stdin and stdout. Instead it should read the input from a list of lines
-- and capture the output into a list of lines. That way we can control the
-- input to `thrice` and assert that its output is correct.

-- First we're going to make one more effect to help us interact with HSpec.
-- The `ShouldBe` operation asserts that the left hand side side and right hand
-- side are equal.
data HSpec :: Effect where
  ShouldBe :: (Show a, Eq a) => a -> a -> HSpec m ()

shouldBe :: (Show a, Eq a, HSpec `Member` es) => a -> a -> Eff ef es ()
shouldBe actual expected = send $ ShouldBe actual expected

runHSpec :: (ef Identity, EIO `Member` es) => Eff ef (HSpec : es) a -> Eff ef es a
runHSpec = interpret_ \case
  ShouldBe actual expected -> liftIO $ actual `Test.shouldBe` expected

runTest :: Eff Anything [HSpec, EIO] a -> Test.Expectation
runTest = void . runEffIO . runHSpec

-- Our test implementation of `Terminal` accepts a list of lines as input and
-- returns the list of lines that were output. Note the new `ef (OutputResult
-- [String])` constraint. Internally our interpreter will use an `Output`
-- interpreter that changes the return type of the computation (it adds the
-- output to the returned value). The constraint ensures that any other
-- interpreters will be OK with that. They all should be, but we need the
-- constraint so Haskell can verify it.
runTerminalMock ::
  (HSpec `Member` es, ef (OutputResult [String]), ef Identity) =>
  [String] -> Eff ef (Terminal : es) a -> Eff ef es ([String], a)
runTerminalMock stdin action = do
  -- Here we see a couple new functions. First is `with` which just rearranges
  -- the order of parameters that interpreters take. Normally the action is the
  -- last parameter to the interpreter. That usually looks nice and lets us
  -- write interpreters in a point free way, but it can create awkward
  -- parentheses in cases like this. The `with` function moves the thing we're
  -- interpreting to the beginning of the line to avoid the parentheses. Second
  -- is the `using` function. It introduces private effects that only this
  -- interpreter can use. We're introducing two private effects to. The state
  -- keeps track of what input still needs to be read, and the output keeps
  -- track of what was printed.
  --
  -- What makes an effect "private" as compared to "public"? Consider the
  -- effect stack (`es`). Any effect on the stack can be used by any other
  -- effect above it in the stack. That's what `Member` does: it finds effects
  -- in the stack and exposes them. If it's in the stack, you can use `Member`
  -- to find it. That makes every effect in the stack "public". Let's see why
  -- that's a problem for `runTerminalMock`. This interpreter relies on an
  -- `Output [String]` to track the list of printed lines. We could have made
  -- that dependency public by adding ``Output [String] `Member` es`` to the
  -- type signature up above. If we'd done that though, there would be nothing
  -- stopping other code from also adding ``Output [String] `Member` es`` and
  -- using the output as well. The `Output [String]` effect is so generic that
  -- maybe some other effect might use it for logging. Everything would look
  -- fine until we added logging to our `thrice` function (or added some other
  -- effect to `thrice` which used logging). Suddenly we'd have logs and
  -- captured stdout mixed into the same list! That would break our test and be
  -- a huge pain to debug.
  --
  -- What we'd like to do instead is say that this `Output [String]` can only
  -- be used by this interpreter for `Terminal`. Other code might output to
  -- other `Output [String]`s on the stack, but this one at this position in
  -- the stack is ours only. That's where "private" effects come in. A private
  -- effect is one which only appears on the effect stack within the
  -- interpreter. Since its not on the effect stack any other time, no one else
  -- can access it using `Member` constraints. It makes our code resilient to
  -- things like the thrice logging problem. Private effects are not a
  -- fundamental feature of Theseus, but instead arise from how we can
  -- manipulate the effect stack. The `raise` family of functions (which
  -- `using` calls behind the scenes) add new effects to the stack. By
  -- carefully controlling when effects are added to the stack, we can
  -- effectively hide them until they're needed.
  (unusedInput, output) <- with action $ using (runState stdin . runOutput @[String]) $ interpret_ \case
    WriteLine line -> output [line]
    ReadLine -> do
      nextLine <- fmap head get
      modify @[String] tail
      pure nextLine

  unusedInput `shouldBe` []
  pure output

-- And now we can write a remarkably clean HSpec test to make sure `thrice`
-- works.
testThrice :: SpecWith ()
testThrice = do
  describe "Thrice" do
    it "echos 3 times" $ runTest do
      (output, ()) <- runTerminalMock ["echo"] thrice
      output `shouldBe` ["echo", "echo", "echo"]

-- There we have it. We wrote a program using an effect and tested it with an
-- alternate implementation.

-- ## Higher Order Effects

-- In effect system literature, we differentiate between first order algebraic
-- effects and higher order effects. The difference between the two is similar
-- to the difference between first order functions and higher order functions.
-- A first order function like `head` accepts and returns things that are not
-- functions. A higher order function like `map` accepts a parameter that is
-- a function. The same applies to first and higher order effects. A first
-- order effect (like `Terminal`, `HSpec`, `Output`, and `State`) accepts
-- parameters that are not effectful computations. Higher order effects accept
-- parameters or return values that are effectful computations. A great example
-- would be the `Catch` effect. You can trigger `Catch` with something like
--
-- ```haskell
-- catch (writeLine "inside the catch" >> throw "Whoops!")
--  \thrown -> writeLine thrown
-- ```
--
-- Notice how the parameters to `catch` use the `Eff` type. That's what makes
-- it higher order. Whether an effect is higher order or not is a property of
-- the effect, not the interpretation. You can tell whether an effect is higher
-- order by looking at its GADT definition.
--
-- Theseus is a library that supports higher order effects. In this section,
-- we'll introduce a mix of higher order and first order effects, and show how
-- they interact.

-- Contriving our Terminal example some more, lets say we wanted to reuse our
-- `thrice` program, but we wanted it to read and write to files instead of
-- stdout and stdin. Keeping `thrice` the exact same, we'll define a new
-- implementation of `Terminal` (in reality you'd probably not call the effect
-- Terminal anymore, but for the sake of our example we'll stick with it).
-- In this example we'll define a first order effect for interacting with
-- files, then we'll introduce a higher order effect for managing open files.

-- ### Managing File Resources

-- This is just a specially named Proxy. We need it because we'll be using the
-- `ST` trick to make sure our files can't be used after they're closed.
data OpenFile tag = OpenFile

-- File is a normal first order effect. The higher order effect comes later.
data File tag :: Effect where
  ReadLineFrom :: OpenFile tag -> File tag m String
  WriteLineTo :: OpenFile tag -> String -> File tag m ()

readLineFrom :: File tag `Member` es => OpenFile tag -> Eff ef es String
readLineFrom file = send $ ReadLineFrom file

writeLineTo :: File tag `Member` es => OpenFile tag -> String -> Eff ef es ()
writeLineTo file line = send $ WriteLineTo file line

-- This type signature should look pretty normal except for its use of the `ST`
-- trick.
withFile ::
  (ef Identity, EIO `Member` es) =>
  FilePath ->
  (forall tag. OpenFile tag -> Eff ef (File tag : es) a) ->
  Eff ef es a
-- Here we use the `resource` function. That's an interpreter for the `Input`
-- effect which guarantees that the `close` method will be called when the
-- interpreter is finished. If you're coming with experience in effect systems
-- that have things like `Coroutines` and `Choice` effects, this might set off
-- warning bells for you. Theseus also has those effects, but they don't break
-- `resource`. If you're interested in understanding why, you'll need to dig
-- into some of the other links in the readme. Unfortunately it's complicated.
-- Luckily we don't need to worry about the complicated implementation details
-- to benefit from it.
withFile path action = with (action OpenFile) $ using (resource open close) $ interpret_ \case
  ReadLineFrom OpenFile -> do
    handle <- input
    liftIO $ hGetLine handle
  WriteLineTo OpenFile line -> do
    handle <- input
    liftIO $ hPutStrLn handle line
 where
  open = liftIO $ openFile path ReadWriteMode
  close handle = liftIO $ hClose handle

-- ### An Effect for Managing Effects

-- Next let's create a higher order file system effect to open files.

data FS :: Effect where
  -- Remember that `m` parameter on our effects from before? Now we're using
  -- it! We can call it `m` when we don't really care what it is, and we can
  -- call it `Eff ef es` when we do. It's important to realize that this is not
  -- the same `es` as we see in the interpreter's type signature. Functions
  -- like `interpret` and `using` manipulate the effect stack and introduce new
  -- scopes. There might be effects which are on the effect stack and in scope
  -- where the effect is sent, but which aren't in scope where the effect is
  -- being interpreted. The opposite can be true when private effects are used.
  -- That makes higher order effects trickier to interpret. The difference
  -- between the send effect stack and the interpreter effect stack is subtle
  -- but really important, so I'll repeat it a few times in different ways as
  -- we go.
  Open ::
    ef Identity =>
    FilePath ->
    (forall tag. OpenFile tag -> Eff ef (File tag : es) a) ->
    FS (Eff ef es) a

open ::
  (FS `Member` es, ef Identity) =>
  FilePath ->
  (forall tag. OpenFile tag -> Eff ef (File tag : es) a) ->
  Eff ef es a
open path action = send $ Open path action

runFS :: (ef Identity, EIO `Member` es) => Eff ef (FS : es) a -> Eff ef es a
-- We're using `interpret` instead of `interpret_`. That changes a couple
-- things.
--
-- First we get an extra `sender` parameter. With that parameter, we can turn
-- a proof that an effect is in scope where the interpreter is running into
-- a proof that the effect is in scope where the effect is being sent. The two
-- effect stacks might not be the same if you have something such as
-- `runFS $ runSomethingElse $ open "x"`. At the interpreter level, we just
-- have `es`, but where `send` is used we have `SomethingElse : FS : es`. There
-- are more effects available where `send` was called, but they both have
-- a subset of the list that's shared.
--
-- Second it changes the return type. Instead of returning an `Eff ef es x`, we
-- return an `Eff ef es (Eff efSend esSend x)`. The *send types represent the
-- effect stack where the effect was sent. That nested `Eff` can be tricky to
-- wrap your head around. In both cases, the `x` variable represents whatever
-- type the effectful program needs to continue. In the first order case, we
-- can use any of the effects that are in scope for the interpreter (aka
-- effects that are in `es`) to calculate that value. In the higher order case
-- that's still true: we can still use any effects that are in scope for the
-- interpreter to calculate a value for `x`. What we gain though is the ability
-- to use effects that are in scope where the effect was sent (aka effects that
-- are in `esSend`). This allows us to interpret higher order effects because
-- the effect we're interpreting has type `FS (Eff efSend esSend) x`. We can
-- use the higher order parameters while calculating a value for `x`.
runFS = interpret \sender (Open path action) ->
  -- We have to use `sender` so that the `EIO` constraint from `es` can be used
  -- in `esSend`. When you use `sender`, you'll always get the original effect.
  -- It doesn't really matter with `EIO`, but imagine we were doing
  -- `sender @(Input String)`. Also imagine that `esSend` were equal to
  -- `Input String : es`. Now we have a predicament. We know there's an
  -- `Input String` within `es` (`sender` only works when that's true) but we
  -- also have the `Input String` outside of `es`. The two might have different
  -- interpreters. Which would run? Although not all effect systems agree on
  -- this, Theseus picks the one somewhere in `es`. It's this behavior which
  -- makes `using` work. This behavior also prevents spooky action at
  -- a distance and leaking effect implementations. If you want the other
  -- behavior, you should add a `Member` constraint to the GADT. Then you won't
  -- have to use `sender` and the highest interpreter will be used. That would
  -- look like ``Open :: EIO `Member` es => ...``. That also makes it clear to
  -- users of your effect that they have control over how the effect will be
  -- interpreted
  pure $ sender @EIO $ withFile path action

-- That was a lot! We went through a bunch of features. To summarize, we saw
-- how higher order effects work and how `resource` allows us to run
-- finalizers. As an aside, you might be wondering how `withFile` (and
-- consequently `Open`) work when something like the `Choice` effect is used.
-- It turns out perfectly fine! I won't get into the details here (effects
-- which manipulate control flow are very rare and they would add a lot of
-- complexity to the tutorial), but if you're curious look into the
-- implementation of `Choice`. Even when Choice (or Coroutine) are used, the
-- file will be closed promptly and will never be used after it's closed.

-- Now to put it all together in our final `Terminal` interpretation. You'll
-- notice we made `FS` a public dependency for `runTerminalFile`. This means
-- effects can share its implementation, and it makes mocking out the `FS`
-- implementation possible. Private effect dependencies on the other hand are
-- useful when you don't want the dependency to be shared. That gives us three
-- ways of providing a dependency: we can make it private using `using`, we can
-- make it public to our interpreter (like `FS` in this case or `EIO` in almost
-- all cases), or we can make it public for the Effect. The last is the most
-- public (all interpreters inherit the dependency and senders can see it) and
-- the first is the least (no one can observe the dependency).
runTerminalFile :: (ef Identity, FS `Member` es) => String -> String -> Eff ef (Terminal : es) a -> Eff ef es a
runTerminalFile input output action = open input \ifile -> open output \ofile -> do
  -- Because of the lambdas, we have to use the lower level `raising` method to
  -- create our private effects. `raising` uses a class to calculate the
  -- difference between the stack of `action` and where we want `action` to
  -- run. It will call `raiseUnder` until the two match. You can always insert
  -- effects into arbitrary locations of the stack, but you can only remove
  -- effects by interpreting them.
  let raisedAction = raising action
  with raisedAction $ interpret_ \case
    ReadLine -> readLineFrom ifile
    WriteLine line -> writeLineTo ofile line

-- And here's a test making sure it works.
testFileThrice :: SpecWith ()
testFileThrice = do
  describe "Thrice" do
    it "works correctly with files" $ runTest $ runFS do
      () <- runTerminalFile "thriceInput.txt" "thriceOutput.txt" thrice
      output <- open "thriceOutput.txt" $ replicateM 3 . readLineFrom
      -- You'll have to check the repo to verify that "file" is the contents of
      -- the input file.
      output `shouldBe` ["file", "file", "file"]

-- ## The End

-- Thanks for getting this far! If you're new to effect systems, hopefully this
-- wasn't too whirlwind of a tour. Effect systems are really cool and I hope
-- you give them a try. If there's anything that would make Theseus easier to
-- use or learn, let me know! If you're experienced with effect systems,
-- hopefully Theseus feels familiar while also having some powerful new
-- additions. The repository's readme links to other documents that dig into
-- what makes Theseus special.
