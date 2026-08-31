# Difference from `origin/master`

This inventory compares the working branch with the local ref
`remotes/origin/master` at commit `7349a6bf`.  It is deliberately separate
from the qubit development area.

## What is branch-only

The selected master ref has no `PhyslibAlpha/Unbounded/QuantumMechanics/OperatorAlgebra/Unbounded`
tree.  Therefore every source file currently under that path is outside
master and belongs to this branch's general unbounded-operator development.
The files are now physically separated by role:

* `Unbounded/Core`
* `Unbounded/Spectral`
* `Unbounded/Affiliation`
* `Unbounded/Calculus`
* `Unbounded/Representation`
* `States` and `Measurement`
* `Unbounded/Dynamics`
* `Unbounded/Examples`
* `Unbounded/Tests`

The surrounding abstract operator-algebra additions are likewise grouped in
their existing purpose-based directories: `WStarAlgebra`, `TraceClass`,
`FiniteDim`, `Measurement`, `Observables`, and `Dynamics`.  The root
`Unbounded.lean` is the stable public entry point for the branch-only API.

The related `QuantumMechanics/Operators` directory is a mixed baseline and
extension area, so its status is recorded explicitly:

| Current location | Relation to `origin/master` |
| --- | --- |
| `Operators/Core/Unbounded.lean` | relocation of master `Operators/Unbounded.lean` |
| `Operators/Canonical/*` | relocations of master canonical operator files |
| `Operators/OneDimension/*` | master files, with branch edits where applicable |
| `Operators/StateObservables/*` | master files, with branch edits where applicable |
| `Operators/SpectralTheory/{Basic,SelfAdjoint,SpectralMeasure,Symmetric}.lean` | master files, with branch edits where applicable |
| `Operators/Multiplication/Basic.lean` | relocation of master `Operators/Multiplication.lean` |
| `Operators/Multiplication/{Core,Spectral,MomentumSpectral,PositionSpectral}.lean` | branch-only extensions |
| `Operators/SpectralTheory/{BoundedSesquilinear,KatoRellich,SpectralTypeDecomposition,Stone,UnboundedSpectralIntegral,WeakSpectralMeasure}.lean` | branch-only extensions |
| `Operators/Applications/HardyInequality.lean` | branch-only application |

Thus the branch-only operator files are visibly identifiable as the extension
rows above, while the relocated master material remains in the corresponding
general-purpose folders.  This keeps mathematical organization separate from
Git history without putting application code into the general algebra API.

To reproduce the committed comparison:

```text
git diff --name-status remotes/origin/master...HEAD \
  -- PhyslibAlpha/Unbounded/QuantumMechanics/OperatorAlgebra
```

To audit the complete current working-tree inventory, including files not yet
committed:

```text
rg --files PhyslibAlpha/Unbounded/QuantumMechanics/OperatorAlgebra
```

## What is intentionally not classified here

`QuantumMechanics/Qubit` is application/development work and is excluded from
this reorganization.  The harmonic oscillator is also treated as an
application: its files were not moved into the general API folders.  Existing
master-side operator files outside `OperatorAlgebra` remain where they were;
the import paths that depended on moved unbounded modules were updated to the
new names.

## Public compatibility boundary

Consumers should import:

```lean
import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Unbounded
```

The internal module names now communicate their role, but the umbrella import
is the supported boundary.  Examples and smoke tests are intentionally not
re-exported by that umbrella.
