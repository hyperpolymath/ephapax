module Ephapax.Affine.Emit

import Ephapax.IR.Decode
import Ephapax.IR.AST

%default total

public export
covering
emitModule : Module -> String
emitModule = encode
