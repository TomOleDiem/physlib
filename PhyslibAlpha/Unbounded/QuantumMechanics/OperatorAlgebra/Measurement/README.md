# Measurement layer

This folder owns the observable-to-statistics interface.

* `PVM` is the norm-valued projection-valued measure on an arbitrary measurable outcome space.
* `NormalPVM` is its infinite-dimensional normal variant: countable additivity is tested by normal
  states rather than imposed in operator norm.
* `POVM` is the norm-valued positive-operator-valued measure.
* `NormalPOVM` is the corresponding weak/normal infinite-dimensional interface.
* `FinitePOVM` records one effect per finite outcome and proves the normalized Born probability
  vector. `FiniteDimensional` specializes this interface to `B(H)` without choosing a basis.

States are deliberately not defined here. State objects, density operators, expectations, and
state-dependent distributions live in `../States`.
