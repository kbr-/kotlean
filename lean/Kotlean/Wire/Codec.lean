import Kotlean.Equality

namespace Kotlean.Wire

structure Codec (α : Type) where
  write : α → List UInt8
  read : List UInt8 → Option (α × List UInt8)
  roundTrip : ∀ value tail, read (write value ++ tail) = some (value, tail)
  sound : ∀ input value rest, read input = some (value, rest) → input = write value ++ rest
  positive : ∀ value, 0 < (write value).length

end Kotlean.Wire
