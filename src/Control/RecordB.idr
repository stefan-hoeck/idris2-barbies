module Control.RecordB

import Monocle.Lens

%default total

public export
interface RecordB (0 k : Type) (0 t : (k -> Type) -> Type) | t where
  constructor MkRecordB
  field : (0 f : k -> Type) -> (v : k) -> Lens' (t f) (f v)

export %inline
field' : RecordB k t => (v : k) -> Lens' (t f) (f v)
field' = field f

export %inline
getField : RecordB k t => (v : k) -> t f -> f v
getField v = get_ (field f v)

export %inline
setField : RecordB k t => (v : k) -> f v -> t f -> t f
setField v = setL (field f v)
