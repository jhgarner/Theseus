module Writer where

import Data.Char (toUpper)
import Theseus.Eff
import Theseus.Effect.Writer
import Utils

testWriter :: SpecWith ()
testWriter = do
  describe "Writer" do
    it "combines multiple tells" do
      ("abc", ()) === runEff $ runWriter do
        tell "a"
        tell "b"
        tell "c"
    describe "Listen" do
      it "works" do
        ("abcde", "cd") === runEff $ runWriter do
          tell "a"
          tell "b"
          (told, ()) <- listen @String do
            tell "c"
            tell "d"
          tell "e"
          pure told
      it "can be nested multiple times" do
        ("abcdefg", ("cdef", "de")) === runEff $ runWriter do
          tell "a"
          tell "b"
          (told, innerTold) <- listen @String do
            tell "c"
            (told, ()) <- listen @String do
              tell "d"
              tell "e"
            tell "f"
            pure told
          tell "g"
          pure (told, innerTold)
    describe "Pass" do
      it "works" do
        ("abCDe", ()) === runEff $ runWriter do
          tell "a"
          tell "b"
          pass @String do
            tell "c"
            tell "d"
            pure (fmap toUpper, ())
          tell "e"
      it "can be nested" do
        ("abCD EFg", ()) === runEff $ runWriter do
          tell "a"
          tell "b"
          pass @String do
            tell "c"
            tell "d"
            pass @String do
              tell "e"
              tell "f"
              pure ((" " ++), ())
            pure (fmap toUpper, ())
          tell "g"
