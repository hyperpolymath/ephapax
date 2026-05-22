-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
module Ephapax.Affine.Emit

import Ephapax.IR.Decode
import Ephapax.IR.AST

%default total

public export
covering
emitModule : Module -> String
emitModule = encode
