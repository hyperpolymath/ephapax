module Ephapax.Parse.TestMain

import Ephapax.Parse.Tests

%default total

main : IO ()
main = do
  _ <- runTests
  pure ()
