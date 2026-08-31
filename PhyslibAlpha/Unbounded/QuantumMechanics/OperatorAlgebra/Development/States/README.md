# Development states

The first state slice should remain completely general over `OperatorAlgebra A`:

* use the existing positive normalized functional `State A`;
* add only coercion, expectation, and elementary positivity/normalization facts;
* keep uncertainty, density operators, trace class, normal states, and unbounded
  distributions in later modules.

The target public dependency is `OperatorAlgebra.Basic` only (plus the small
observable lemmas needed by the statement).  In particular, importing a state
must never import W⋆ or unbounded spectral theory.
