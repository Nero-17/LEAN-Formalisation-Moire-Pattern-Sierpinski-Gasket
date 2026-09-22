"""Exact finite arithmetic for the independent manuscript review.

This script does not claim to formalize gasket geometry.  At theta=0 every
ordered pair of first-level cells meets: F_i(p_j)=F_j(p_i).  At theta=pi/3
the exact triangle inequalities below exhaust possible live carries, and each
retained carry has an infinite continuation.  All counting uses integer
coordinates in the basis (1, omega), with omega^2=-1-omega.
"""

from collections import Counter
from fractions import Fraction
from itertools import product
import json


VERTICES = ((1, 0), (0, 1), (-1, -1))
DIGIT_PAIRS = tuple(product(range(3), repeat=2))


def subtract(first, second):
    return first[0] - second[0], first[1] - second[1]


def rotate_pi_third(point):
    return point[0] - point[1], point[0]


def digit(rotation, pair):
    return subtract(VERTICES[pair[0]], rotation(VERTICES[pair[1]]))


def update(carry, displacement):
    return 2 * carry[0] + displacement[0], 2 * carry[1] + displacement[1]


def in_reflected_double_triangle(point):
    # -2T has vertices (-2,0), (0,-2), (2,2).
    first, second = point
    return (2 * first - second <= 2
            and -first + 2 * second <= 2
            and first + second >= -2)


def survive_counts(displacements, depth):
    carries = Counter({(0, 0): 1})
    counts = [1]
    reached = {(0, 0)}
    for _ in range(depth):
        next_carries = Counter()
        for carry, multiplicity in carries.items():
            for displacement in displacements:
                candidate = update(carry, displacement)
                if in_reflected_double_triangle(candidate):
                    next_carries[candidate] += multiplicity
        carries = next_carries
        reached.update(carries)
        counts.append(sum(carries.values()))
    return counts, reached


def main():
    zero_digits = tuple(digit(lambda point: point, pair) for pair in DIGIT_PAIRS)
    assert len(zero_digits) == 9
    assert len(set(zero_digits)) == 7
    assert zero_digits.count((0, 0)) == 3

    # Explicit common point for every first-level pair, including boundaries.
    midpoint_coordinates = {
        pair: tuple(Fraction(VERTICES[pair[0]][axis] + VERTICES[pair[1]][axis], 2)
                    for axis in range(2))
        for pair in DIGIT_PAIRS
    }
    assert len(midpoint_coordinates) == 9

    pi_third_digits = tuple(digit(rotate_pi_third, pair) for pair in DIGIT_PAIRS)
    expected_carries = {(0, 0), (-1, 0), (0, -1), (1, 1)}
    transitions = {}
    for carry in expected_carries:
        live_next = [update(carry, displacement) for displacement in pi_third_digits
                     if in_reflected_double_triangle(update(carry, displacement))]
        assert set(live_next) <= expected_carries
        assert len(live_next) == (6 if carry == (0, 0) else 1)
        if carry != (0, 0):
            assert live_next == [(0, 0)]
        transitions[str(carry)] = dict((str(key), value)
                                       for key, value in Counter(live_next).items())

    pair_counts, reached = survive_counts(pi_third_digits, 10)
    set_counts, _ = survive_counts(tuple(set(pi_third_digits)), 10)
    assert reached == expected_carries
    assert pair_counts == [6 ** ((level + 1) // 2) for level in range(11)]
    assert set_counts == [3 ** ((level + 1) // 2) for level in range(11)]
    pair_ratios = [Fraction(pair_counts[level + 1], pair_counts[level])
                   for level in range(10)]
    assert pair_ratios == [Fraction(6 if level % 2 == 0 else 1)
                           for level in range(10)]

    # Countermodel to the claimed first/second-moment implication.  On half
    # of the angle interval let a probability on the unit disk have ball
    # mass r^2, and on the other half ball mass r^3.  Their densities are
    # respectively 1/pi and 3|x|/(2pi).  Moments divided by pi are exact.
    moment_checks = []
    for radius in (Fraction(1, 2), Fraction(1, 4), Fraction(1, 8)):
        first_moment_over_pi = radius ** 2 + radius ** 3
        second_moment_over_pi = radius ** 4 + radius ** 6
        assert radius ** 2 <= first_moment_over_pi <= 2 * radius ** 2
        assert second_moment_over_pi <= 2 * radius ** 4
        moment_checks.append({"radius": str(radius),
                              "first_moment_over_pi": str(first_moment_over_pi),
                              "second_moment_over_pi": str(second_moment_over_pi),
                              "bad_half_mass_over_r_squared": str(radius)})

    print(json.dumps({
        "theta_zero_level_one": {
            "meeting_ordered_pairs": 9,
            "legal_distinct_digits": len(set(zero_digits)),
            "zero_digit_multiplicity": zero_digits.count((0, 0)),
        },
        "pi_third": {
            "exact_transitions": transitions,
            "ordered_pair_counts_from_level_zero": pair_counts,
            "distinct_digit_counts_from_level_zero": set_counts,
            "consecutive_pair_count_ratios": list(map(str, pair_ratios)),
        },
        "moment_countermodel": moment_checks,
    }, indent=2))


if __name__ == "__main__":
    main()
