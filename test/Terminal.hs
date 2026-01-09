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

-- This module acts as a tutorial for Theseus. If you're familiar with other
-- effect systems, it should all be pretty similar. If not, hopefully it walks
-- you through the basics. Regardless of your experience level, reach out if
-- you have any questions!
--
-- When you use an effect system library, you'll end up with a pyramid of
-- effects. At the bottom of the pyramid are low level generic effects. Those
-- are used to implement more specific higher level effects. Instead of only
-- composing functions, you can also think of composing effects. Since effects
-- can be easily swapped out, you can mock any part of your effect stack. This
-- makes it easy to write anything ranging from unit tests to integration
-- tests. In general, functions should have a very small number of effects
-- associated with them. If a function's signature begins to grow unwieldy, it
-- probably means you need to introduce a new effect to abstract away
-- something.

-- ## First Order Effects

-- Let's jump into how you use Theseus. Our goal is to implement
-- a Terminal effect that interacts with stdin and stdout. We'll also include
-- a test implementation and a test program that we can verify. This is
-- a common example across effect system libraries because it matches the
-- common case. Most effects will be like the Terminal effect: domain specific
-- and fairly simple. In general you should never be afraid of introducing new
-- effects.

-- Effects are defined as GADTs. Each operation that the effect performs will
-- be a constructor of the GADT.
data Terminal :: Effect where
  -- This operation accepts a String parameter and returns `()`. The `m` is there
  -- in case our effect were higher order. We don't need to worry about it now.
  WriteLine :: String -> Terminal m ()
  -- This operation has no parameters and returns a String.
  ReadLine :: Terminal m String

-- Now for some helper functions. Most effect systems use template haskell to
-- generate these. Theseus doesn't have that yet. They're boring boilerplate,
-- but we'll use them to show a couple new concepts.

-- A few things are introduced in this line. `Eff` is the Monad that our effect
-- system runs in. The `ef` parameter we'll ignore for now. The `es` parameter
-- is a type level list of effects. By making `es` generic, we're saying that
-- (almost) any list of effects will work. The `Member` constraint limits the
-- list to lists that contain `Terminal`. The final parameter to Eff is the
-- return type of the effectful computation.
writeLine :: Terminal `Member` es => String -> Eff ef es ()
-- The send function takes an Effect and prepares it to be executed. The `send`
-- function doesn't say anything about how it'll be executed.
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

-- Hopefully that's not too hard to follow. We're once again using our `Eff`
-- and `Member` types. The last thing we need is a way to run `thrice`. For
-- that we'll need an interpreter for `Terminal` effects.

-- Here we see our first use of `ef`. Honestly, `ef` is kind of messy and it's
-- best just to add it whenever the compiler errors tell you to. The `ef`
-- variable is a Constraint on how interpreters are allowed to modify the
-- effectful computation's return type. Technical all interpreters wrap the
-- computation in some Functor. Most of the time that's `Identity`, so the
-- `interpret` function handles the wrapping and unwrapping for you. By adding
-- `ef Identity` as a constraint, we're saying that `Identity` must be
-- a wrapper that all other interpreters know how to handle. Once again, we
-- don't really care much about `ef` most of the time. Usually effect
-- interpreters support all wrappers and use the `Identity` wrapper themselves.
-- We only need this because a handful of uncommon (but powerful) interpreters
-- require it.
--
-- The other constraint we have is for the `EIO` effect. EIO says that we can
-- lift arbitrary IO operations into `Eff`. When `EIO` is a member of the
-- effect stack, `Eff` implements `MonadIO`.
runTerminal :: (ef Identity, EIO `Member` es) => Eff ef (Terminal : es) a -> Eff ef es a
-- There are a few different interpret functions. The most general
-- `interpretRaw` gives you a ton of control flow flexibility, but requires
-- a lot of boilerplate and manual verification. We won't cover it in this
-- tutorial. The next most general is `interpretW` which is used by
-- interpreters that need to wrap the output in something other than
-- `Identity`. Finally is `interpret` which is for interpreters that don't need
-- to change the result type in any way. When there's an `_` at the end of the
-- name, it means it's specialized for first order effects. We'll look at an
-- example of a higher order effect later.
runTerminal = interpret_ \case
  WriteLine line -> liftIO $ putStrLn line
  ReadLine -> liftIO getLine

-- Now we have everything we need to turn our `thrice` function into something
-- Haskell can actually run.
thriceIO :: IO ()
-- The runEffIO function turns a effect stack that only contains the `EIO`
-- effect into an IO operation.
thriceIO = runEffIO $ runTerminal thrice

-- So far all we've done is introduce a lot of complexity for little gain. To
-- show why effect systems are powerful, let's add some test code.

-- This effect allows us to interact with HSpec within our computation. You
-- wouldn't use it in production, but test code will find it helpful.
data HSpec :: Effect where
  ShouldBe :: (Show a, Eq a) => a -> a -> HSpec m ()

shouldBe :: (Show a, Eq a, HSpec `Member` es) => a -> a -> Eff ef es ()
shouldBe actual expected = send $ ShouldBe actual expected

-- This interpreter assumes that `HSpec` and `EIO` will be the last two
-- effects. It would also be valid (and probably cleaner) to write a `runTest`
-- interpreter that composes with `runEffIO`.
runTest :: Eff Anything [HSpec, EIO] a -> Test.Expectation
runTest = void . runEffIO . interpret_ \(ShouldBe actual expected) -> liftIO $ actual `Test.shouldBe` expected

-- And here's our test implementation of `Terminal`. It accepts a list of lines
-- as input and returns the list of lines that were output. Note the new `ef
-- (OutputResult [String])` constraint. Internally our interpreter uses an
-- Output interpreter that changes the return type of the computation (it adds
-- the output to the returned value). The constraint ensures that any other
-- effect interpreters will be OK with that. They all should be.
runTerminalMock :: (HSpec `Member` es, ef (OutputResult [String]), ef Identity) => [String] -> Eff ef (Terminal : es) a -> Eff ef es ([String], a)
runTerminalMock stdin action = do
  -- Here we see a couple new functions. First is `with` which just rearranges
  -- the order of parameters that interpreters take. Normally the action is the
  -- last parameter to the interpreter, but that can create awkward parentheses
  -- in cases like this. The `with` function fixes that. Second is the `using`
  -- function. It introduces private effects that only this interpreter can use.
  -- We're introducing two private effects. The State keeps track of what input
  -- still needs to be read and the output keeps track of what was printed.
  -- Because we're using `using`, none of the code within `action` can use
  -- these effects. Similarly, they're gone as soon as our interpreter finishes
  -- running. That all is what makes them private.
  (unusedInput, output) <- with action $ using (runState stdin . runOutput @[String]) $ interpret_ \case
    WriteLine line -> output [line]
    ReadLine -> do
      -- We'll use partial functions since it's fine if our test throws
      -- Exceptions.
      nextLine <- fmap head get
      modify @[String] tail
      pure nextLine

  unusedInput `shouldBe` []
  pure output

-- Now we can write an HSpec test for our thrice function.

testThrice :: SpecWith ()
testThrice = do
  describe "Thrice" do
    it "echos 3 times" $ runTest do
      (output, ()) <- runTerminalMock ["echo"] thrice
      output `shouldBe` ["echo", "echo", "echo"]

-- There we have it. We wrote a program using an effect and tested it with an
-- alternate implementation.

-- ## Higher Order Effects

-- Contriving our example some more, lets say we want to reuse our `thrice`
-- program, but we want it to read and write to files instead of stdout and
-- stdin. Keeping `thrice` the exact same, we'll define a new implementation of
-- `Terminal` (in reality you'd probably not call the effect Terminal anymore,
-- but for the sake of our example we'll stick with it). First we need an
-- effect for interacting with files.

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
withFile :: (ef Identity, EIO `Member` es) => FilePath -> (forall tag. OpenFile tag -> Eff ef (File tag : es) a) -> Eff ef es a
-- Here we use the `resource` function. That's an interpreter for the `Input`
-- effect which guarantees that the close method will be called when the
-- interpreter is finished. If you're coming with experience in effect systems
-- that have things like `Coroutines` and `Choice` effects, this might set off
-- warning bells for you. Theseus also has those effects, but they don't break
-- `resource`.
withFile path action = with (action OpenFile) $ using (resource open close) $ interpret_ \case
  ReadLineFrom OpenFile -> do
    -- Within the scope of our `File` interpreter, we can use the private
    -- `input` to get the file handle.
    handle <- input
    liftIO $ hGetLine handle
  WriteLineTo OpenFile line -> do
    handle <- input
    liftIO $ hPutStrLn handle line
 where
  open = liftIO $ openFile path ReadWriteMode
  close handle = liftIO $ hClose handle

-- Next let's create a higher order file system effect to open files.

data FS :: Effect where
  -- Here we see how the previously unused type parameter for our `Effect`
  -- GADTs encodes the higher order information. That parameter represents the
  -- effect stack at the time our effect was sent. It's important to realize
  -- that this will not be the same effect stack as when the effect was
  -- interpreted. We'll see why that matters in the interpreter and I'll repeat
  -- this a few times in a few different ways because it's essential for
  -- understanding higher order effects.
  Open :: ef Identity => FilePath -> (forall tag. OpenFile tag -> Eff ef (File tag : es) a) -> FS (Eff ef es) a

open :: (FS `Member` es, ef Identity) => FilePath -> (forall tag. OpenFile tag -> Eff ef (File tag : es) a) -> Eff ef es a
open path action = send $ Open path action

runFS :: (ef Identity, EIO `Member` es) => Eff ef (FS : es) a -> Eff ef es a
-- We're using `interpret` instead of `interpret_`. That changes a couple
-- things. First we get an extra `sender` parameter. With that parameter, we
-- can turn a proof that an effect is in scope when the interpreter was running
-- into a proof that the effect is in scope when the effect was sent. The two
-- effect stacks might not be the same if you have something such as
-- `runFS $ runSomethingElse $ open "x"`. At the interpreter level, we have
-- `es`, but where `open` is called we have `SomethingElse : es`.
runFS = interpret \sender (Open path action) ->
  -- The other thing that changes is the return type. Instead of returning an
  -- `Eff ef es x`, we return an `Eff ef es (Eff efSend esSend x)`. The *send
  -- types represent the effect stack where the effect was sent. We're creating
  -- a computation where the interpreter was running to create a computation
  -- where the effect stack was sent to create the value that our program needs
  -- to continue. We have to use `sender` so that the `EIO` constraint in `es`
  -- can be used in `esSend`. When you use `sender`, you'll always get the
  -- original effect. It doesn't really matter with `EIO`, but imagine we were
  -- doing `sender @(Input String)`. Also imagine that `esSend` was equal to
  -- `Input String : es`. Now we have a predicament. We know there's an `Input
  -- String` within `es` (`sender` only works when that's true) but we also
  -- have a higher `Input String` on the stack. Which interpreter would run?
  -- Although not all effect systems agree on this, Theseus picks the one
  -- somewhere in `es`. It's this behavior which makes `using` work. This
  -- behavior also prevents spooky action at a distance and leaking effect
  -- implementations. If you want the other behavior, you should add a `Member`
  -- constraint to the GADT. Then you won't have to use `sender` and the
  -- highest interpreter will be used. That would look like
  -- ``Open :: EIO `Member` es => ...``.
  pure $ sender @EIO $ withFile path action

-- That was a lot! We went through a whirlwind of features. To summarize, we
-- saw how higher order effects work and how `resource` allows us to run
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
-- public (all interpreters inherit the dependency) and the first is the least
-- (no one can observe the dependency).
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

-- Thanks for getting this far! If you're new to effect systems, hopefully this
-- wasn't too whirlwind of a tour. Effect systems are really cool and I hope
-- you give them a try. If there's anything that would make Theseus easier to
-- use or learn, let me know! If you're experienced with effect systems,
-- hopefully Theseus feels familiar while also having some powerful new
-- additions. The repository's readme links to other documents that dig into
-- what makes Theseus special.
