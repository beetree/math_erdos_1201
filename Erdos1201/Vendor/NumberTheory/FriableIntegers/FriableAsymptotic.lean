module

public import Erdos1201.Vendor.NumberTheory.FriableIntegers.FriableAsymptoticPart1
public import Erdos1201.Vendor.NumberTheory.FriableIntegers.FriableAsymptoticPart2
public import Erdos1201.Vendor.NumberTheory.FriableIntegers.FriableAsymptoticPart3
public import Erdos1201.Vendor.NumberTheory.FriableIntegers.FriableAsymptoticPart4

@[expose] public section

/-!
# Friable counts on the main friable-integer estimate scale

Aggregator for the split pieces.  All declarations live in the part files under
the `FriableIntegers.FriableAsymptotic` namespace.
-/

open scoped BigOperators
open Filter Topology Asymptotics

namespace FriableIntegers.FriableAsymptotic

open ArithmeticModel DickmanBasic Scale

end FriableIntegers.FriableAsymptotic
