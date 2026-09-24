# Numerical computations in Section 4.2

With NumPy installed, run `python numerics/survivor_counts.py`.
This regenerates `survivor_counts.csv` (all depths 0 through 20 at four
non-resonant angles) and `survivor_plot.dat` (the normalised counts used
by the Section 4.2 curve). Each retained row represents an ordered address
pair, including multiplicities when relative displacements coincide.
The membership polygon is the convex hull of the nine vectors
`R_theta p_j - p_i`, including its boundary. Processing is chunked to
reduce temporary memory use. The largest count is 49,215,285;
allow several GB of available memory.

Every count is compared at absolute distance tolerances `1e-10` and `1e-8`.
The script also checks the exact known counts at pi/3 through depth 12
and at angle zero through depth 1. Tolerance agreement is a diagnostic,
not interval certification or a convergence proof.

With Matplotlib also installed, run `python numerics/dimension_plot.py`.
This produces `growth_fits.csv` and `figures/dimensions-comparison.pdf`
(plus a PNG preview). Fits are ordinary least squares with an intercept
for log2(count) against depth. All red points use the same interval 16--20;
the table also reports intervals 8--12 and 18--20. The CSV includes longer
windows to make window dependence visible. These slopes are finite-scale
growth estimates, not certified Hausdorff or box dimensions.

The blue points use the pre-existing `data/mtheta_data.dat`: 218 records,
including reflection symmetry, with columns `theta` (degrees), `dim`
(numerically evaluated dimension) and `c` (log10 of the Eisenstein norm N).
Recorded N values range from 7 to 597. At resonant angles, the theorem
identifies the dimension exactly as log2 of the transition matrix's spectral
radius; only its decimal evaluation is numerical. The plot displays angular
variation of these dimensions. Symmetry cases, outside the plotted vertical
range, are reported separately in the table.
The original matrix-generation code and exact spectral certificates are not
included here; these scripts preserve, rather than regenerate, that dataset.

Run these commands from the repository root. Install dependencies with `python -m pip install -r numerics/requirements.txt`. The counting script can require several GB of RAM; the plotting script can be run directly using the included counts. No manuscript source or text is included.
