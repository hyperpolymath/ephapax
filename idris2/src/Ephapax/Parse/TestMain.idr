-- SPDX-License-Identifier: MPL-2.0
// Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
module Ephapax.Parse.TestMain

import Ephapax.Parse.Tests

%default total

main : IO ()
main = do
  _ <- runTests
  pure ()
