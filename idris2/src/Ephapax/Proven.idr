module Ephapax.Proven

import Proven.SafeString.Escape

%default total

public export
escapeSExprString : String -> String
escapeSExprString = escapeJSON
