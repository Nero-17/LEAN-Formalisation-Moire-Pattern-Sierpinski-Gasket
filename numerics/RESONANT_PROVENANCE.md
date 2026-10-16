# Recovered resonant matrix construction

`resonant_audit_original.py` is a byte-for-byte copy of the independent
integer-coordinate reconstruction used in the September 2026 manuscript
review in the Codex conversation **Moire Pattern**. Its SHA-256 is
`7b9037fc3f8e268f5913c00ef4ca8b6067a8f430b8799cac642c586e1f2c4239`.
The original file was named `audit_resonant_numbers.py`.

This is **not identified as the original generator of the 218 blue points**.
The review itself explicitly distinguished its seven-case reconstruction from
the pre-existing dataset. The conversation **moire pattern 2** contains a
different, square-carpet certificate; that is not the gasket dataset generator.
The historical generator of the complete blue dataset has not been recovered.

`resonant_matrix.py` adapts that recovered reconstruction to export the integer
states and sparse matrix rows to JSON. It adds a command-line interface, rejects
the zero Eisenstein parameter, and exposes the graph; the construction and
spectral calculation are otherwise unchanged.

From the repository root, using Python's standard library:

```sh
python numerics/resonant_matrix.py 3 1 --output resonant-3-1.json
python numerics/check_resonant_recovery.py
```

For `z=m+n*omega`, `omega=exp(2*pi*i/3)`, the rotation is `z/conjugate(z)`.
Coordinates are in the basis `(1, omega)` and scaled by `N=m*m-m*n+n*n`.
The polygon and displacement updates use exact Python integers. A state is a
set of live displacements, initially `{(0,0)}`. For each first-gasket digit,
the union of the three possible second-gasket updates is formed and clipped
to the closed difference polygon. Empty target sets are omitted.

Rows of the matrix are source states. `A[i,j]` is the number of occurrences of
`j` in `transition_targets[i]`; repeated targets count distinct first-gasket
labels. `state_vectors` records the displacement sets in the same state order.
This is a sparse representation; no dense matrix is allocated.

The spectral step applies a shifted power iteration within strongly connected
components. Despite the inherited names `dim_lower` and `dim_upper`, the values
use floating point without directed rounding and **are not certified bounds**.
The iteration cap is 10,000 and the state cap is 200,000; recursive component
enumeration can also reach Python's recursion limit on large examples.

`resonant_recovery_checks.json` records seven representative table checks,
including the symmetry cases, and comparisons with matching stored blue points.
This does not certify or regenerate all 218 records. It is separate from the
Lean proof development and is not itself formally verified.
