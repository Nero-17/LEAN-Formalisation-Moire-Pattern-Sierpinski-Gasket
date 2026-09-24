"""Finite-depth, labelled pair counts for Section 4.2 (requires NumPy).

Each retained row represents an ordered pair of address words. Equal relative
displacements are deliberately not deduplicated. Membership includes the
boundary of R_theta T - T. Floating-point tolerance checks are diagnostics,
not certified exact arithmetic.
"""
import csv
import math
from pathlib import Path

import numpy as np


def convex_hull(points):
    points = sorted(set(map(tuple, points)))

    def cross(a, b, c):
        return (b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0])

    halves = []
    for ordered in (points, points[::-1]):
        half = []
        for point in ordered:
            while len(half) >= 2 and cross(half[-2], half[-1], point) <= 0:
                half.pop()
            half.append(point)
        halves.extend(half[:-1])
    return np.asarray(halves)


def counts(theta, depth, tolerance):
    vertices = np.array([[1., 0.], [-.5, math.sqrt(3) / 2], [-.5, -math.sqrt(3) / 2]])
    rotation = np.array([[math.cos(theta), -math.sin(theta)],
                         [math.sin(theta), math.cos(theta)]])
    rotated = vertices @ rotation.T
    digits = (vertices[:, None, :] - rotated[None, :, :]).reshape(9, 2)
    hull = convex_hull(-digits)
    edges = np.roll(hull, -1, axis=0) - hull
    normals = np.column_stack((-edges[:, 1], edges[:, 0]))
    normals /= np.linalg.norm(normals, axis=1)[:, None]
    thresholds = np.sum(hull * normals, axis=1)
    displacements = np.zeros((1, 2))
    result = [1]
    for _ in range(depth):
        children = []
        for start in range(0, len(displacements), 250000):
            doubled = 2 * displacements[start:start + 250000]
            for digit in digits:
                candidate = doubled + digit
                keep = np.ones(len(candidate), dtype=bool)
                for normal, threshold in zip(normals, thresholds):
                    keep &= candidate[:, 0] * normal[0] + candidate[:, 1] * normal[1] >= threshold - tolerance
                children.append(candidate[keep])
        displacements = np.concatenate(children)
        result.append(len(displacements))
    return result


def main():
    angles = {"pi/4": math.pi / 4, "pi/6": math.pi / 6,
              "pi/12": math.pi / 12, "atan(sqrt(3)/2)": math.atan(math.sqrt(3) / 2)}
    rows = []
    for name, theta in angles.items():
        first = counts(theta, 20, 1e-10)
        second = counts(theta, 20, 1e-8)
        if first != second:
            raise RuntimeError(f"Tolerance-dependent counts at {name}")
        for n, count in enumerate(first):
            rows.append({"angle": name, "depth": n, "count": count,
                         "normalised_count": (4 / 9) ** n * count})
    # Independent exact recurrence from the audited pi/3 example.
    assert counts(math.pi / 3, 12, 1e-10) == [6 ** ((n + 1) // 2) for n in range(13)]
    assert counts(0., 1, 1e-10) == [1, 9]
    path = Path(__file__).with_name("survivor_counts.csv")
    with path.open("w", newline="", encoding="utf-8") as output:
        writer = csv.DictWriter(output, fieldnames=rows[0].keys())
        writer.writeheader()
        writer.writerows(rows)
    plot_path = Path(__file__).with_name("survivor_plot.dat")
    with plot_path.open("w", encoding="utf-8") as output:
        output.write("depth pi_four pi_six pi_twelve atan_sqrt3_half\n")
        for depth in range(21):
            values = [row["normalised_count"] for row in rows if row["depth"] == depth]
            output.write(str(depth) + " " + " ".join(format(value, ".12g") for value in values) + "\n")
    for row in rows:
        if row["depth"] in (12, 16, 20):
            print(row)


if __name__ == "__main__":
    main()
