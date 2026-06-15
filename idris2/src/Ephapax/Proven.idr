-- SPDX-License-Identifier: MPL-2.0
// Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
module Ephapax.Proven

import Proven.SafeString.Escape

%default total

public export
escapeSExprString : String -> String
escapeSExprString = escapeJSON
