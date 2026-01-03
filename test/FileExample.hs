module FileExample where

import Control.Applicative
import Control.Monad.IO.Class
import Control.Monad.Identity
import Data.Functor
import Theseus.Eff
import Theseus.Effect.Choice
import Theseus.Effect.IO
import Theseus.Effect.Input

-- This example shows something that most effect systems can't handle:
-- combining higher order effects, rich control flow, and prompt resource
-- management. Although it's not interacting with real IO to read the file, you
-- can still trace it doing what it should.
testFileExample :: IO ()
testFileExample = void $ runEffIO $ runCollect $ collect $ runFS $ do
  file <- pure "a.txt" <|> pure "b.txt"
  withFile file \handle -> do
    contents <- readHandle handle
    liftIO $ putStrLn $ "read: " ++ contents
    -- In most effect systems, the following line would cause the file to be
    -- closed twice because the control flow is split into two branches.
    somethingElse <- pure "left" <|> pure "right"
    writeHandle handle somethingElse

-- The above program prints:
-- Opening file a.txt
-- I'm reading from a.txt
-- read: Pretend like I'm doing real IO
-- I'm writing "left" to a.txt
-- I'm writing "right" to a.txt
-- closing a.txt now
-- Opening file b.txt
-- I'm reading from b.txt
-- read: Pretend like I'm doing real IO
-- I'm writing "left" to b.txt
-- I'm writing "right" to b.txt
-- closing b.txt now

-- The rest of this file is a dummy filesystem effect. It doesn't interact with
-- real files, but it follows the flow of something that would and it prints
-- useful info whenever a file operation happens.
newtype Handle fs = Handle String -- Pretend like there's real data here

data FS :: Effect where
  WithFile :: ef Identity => String -> (forall fs. Handle fs -> Eff ef (File fs : es) a) -> FS (Eff ef es) a

withFile :: (FS `Member` es, EIO `Member` es, ef Identity) => String -> (forall fs. Handle fs -> Eff ef (File fs : es) a) -> Eff ef es a
withFile s action = send $ WithFile s action

runFS :: (EIO `Member` es, ef Identity) => Eff ef (FS : es) a -> Eff ef es a
runFS = interpret \sender (WithFile file action) -> do
  liftIO $ putStrLn $ "Opening file " ++ file
  pure $ sender @EIO (runFile file action)

data File fs :: Effect where
  ReadHandle :: Handle fs -> File fs m String
  WriteHandle :: Handle fs -> String -> File fs m ()

readHandle :: File fs `Member` es => Handle fs -> Eff ef es String
readHandle handle = send $ ReadHandle handle

writeHandle :: File fs `Member` es => Handle fs -> String -> Eff ef es ()
writeHandle handle s = send $ WriteHandle handle s

runFile :: (ef Identity, EIO `Member` es) => String -> (forall fs. Handle fs -> Eff ef (File fs : es) a) -> Eff ef es a
runFile name act = using (resource openFile closeFile) (interpret_ handle) $ act $ Handle name
 where
  openFile = do
    liftIO $ putStrLn $ "opening " ++ name ++ " now"
    pure $ Handle name
  closeFile (Handle name) = liftIO $ putStrLn $ "closing " ++ name ++ " now"
  handle :: EIO `Member` es => Handler_ (File fs) ef es
  handle (ReadHandle (Handle name)) = do
    liftIO $ putStrLn $ "I'm reading from " ++ name
    pure "Pretend like I'm doing real IO"
  handle (WriteHandle (Handle name) contents) = do
    liftIO $ putStrLn $ "I'm writing " ++ show contents ++ " to " ++ name
    pure ()
