/-!
# Basic Data Structures Formalization
-/

namespace HashTable

/-!
## Hash Tables
Pure functional hash tables are complex due to immutability.
-/

/--
We model a Hash Table here as an `Array` of buckets (using `List (K × V)`
for collision resolution via chaining). This requires the Key type `K` to
implement both `Hashable` and `BEq` (Boolean equality).
-/
structure HashTable (K : Type) (V : Type) [Hashable K] [BEq K] where
  /-- The total number of allocated buckets. -/
  capacity : Nat
  /-- The buckets storing key-value pairs. -/
  buckets : Array (List (K × V))
  /-- A formal proof that the underlying array size always matches the stated capacity. -/
  size_eq : buckets.size = capacity

end HashTable
