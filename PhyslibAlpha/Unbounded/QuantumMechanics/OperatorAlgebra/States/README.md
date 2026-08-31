# State layer

This folder owns state objects and state-dependent analysis. `Basic` defines positive normalized
functionals, `NormalState` adds weak-* continuity, and `Expectation`/`Uncertainty` provide bounded
observable statistics. Density-operator and spectral-distribution modules supply the concrete and
unbounded extensions.

The measurement layer consumes states to produce probability measures; it does not own the state
definition itself.
