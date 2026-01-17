module Ephapax.Affine.Emit

import Ephapax.IR.Decode
import Ephapax.IR.AST

%default partial

public export
emitModule : Module -> String
emitModule = encode
