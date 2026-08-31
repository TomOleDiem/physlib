# Development measurement

The first measurement slice is finite-outcome and works for every
`OperatorAlgebra A`:

* a finite POVM is a finite family of effects summing to `1`;
* a state evaluates each effect to a nonnegative real probability;
* the probabilities sum to `1`.

This is enough for finite-dimensional quantum mechanics and qubits.  It does not
need a measurable outcome space, a predual, or a normal state.

Only after this API is stable should the project add measurable-space PVM/POVM
objects.  Those objects must state whether countable additivity is norm, strong,
or ultraweak; their scalar statistics should live in a separate module.
