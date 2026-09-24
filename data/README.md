# Numerical data

[dimension-results.json](dimension-results.json) contains the 218 blue resonant-angle records and four red finite-depth estimates, including all 84 counts at depths 0--20 and fits over five depth windows per angle. Angles are in degrees. The plotted red estimates use depths 16--20. The normalised counts are `(4/9)^n * count`.

The blue dimensions are numerical spectral-radius evaluations copied at their original precision; this file does not provide the original matrices or certify all 218 values. Red slopes estimate finite-scale count growth, not certified Hausdorff dimensions. The JSON records provenance, arithmetic limitations and source hashes. These numerical data are separate from the Lean proof development.

Read with Python's standard library: `json.load(open("data/dimension-results.json"))`.
