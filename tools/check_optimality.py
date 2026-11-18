"""Check closure and Pareto decisions against the proved interface.

The decisions mirror `Optimality.closure_operator_exact`,
`Optimality.union_misses_cross_consequence`, `Optimality.guardedMaximal`,
`Optimality.paretoMaximal_can_regress`, and `Optimality.reducedAllowed`.
A regressing frontier point, an out-of-universe root, and a project-first
product reduction are refusals.
"""

from __future__ import annotations


def subsets(items: list[int]) -> list[list[int]]:
    out: list[list[int]] = [[]]
    for item in items:
        out.extend([item] + rest for rest in list(out))
    return out


def checked_close(
    universe: list[int], roots: list[int], rules: list[tuple[list[int], int]]
) -> list[int] | None:
    if any(root not in universe for root in roots):
        return None
    if any(head not in universe for _premises, head in rules):
        return None

    def model_ok(candidate: list[int]) -> bool:
        if any(root not in candidate for root in roots):
            return False
        for premises, head in rules:
            if all(premise in candidate for premise in premises) and head not in candidate:
                return False
        return True

    models = [candidate for candidate in subsets(universe) if model_ok(candidate)]
    return [atom for atom in universe if all(atom in model for model in models)]


def dominates(left: tuple[int, int], right: tuple[int, int]) -> bool:
    return (
        left[0] <= right[0]
        and left[1] <= right[1]
        and (left[0] < right[0] or left[1] < right[1])
    )


def no_worse(candidate: tuple[int, int], incumbent: tuple[int, int]) -> bool:
    return candidate[0] <= incumbent[0] and candidate[1] <= incumbent[1]


def pareto_maximal(candidates: list[tuple[int, int]]) -> list[tuple[int, int]]:
    return [
        candidate
        for candidate in candidates
        if not any(dominates(other, candidate) for other in candidates)
    ]


def guarded_maximal(
    incumbent: tuple[int, int], candidates: list[tuple[int, int]]
) -> list[tuple[int, int]]:
    admitted = [candidate for candidate in candidates if no_worse(candidate, incumbent)]
    return pareto_maximal(admitted)


def release_accepts(
    incumbent: tuple[int, int],
    candidate: tuple[int, int],
    candidates: list[tuple[int, int]],
) -> bool:
    return candidate in guarded_maximal(incumbent, candidates)


def reduced_allowed(kind: str) -> bool:
    if kind == "componentwise-sum":
        return True
    if kind == "project-first":
        return False
    raise ValueError(kind)


def classifications() -> list[str]:
    catalogue = [(1, 10), (10, 1)]
    guarded = release_accepts((10, 10), (1, 10), [(10, 10), (1, 10)])
    regressing_frontier = (10, 1) in pareto_maximal(catalogue)
    regressing_release = release_accepts((1, 10), (10, 1), catalogue)
    alone = checked_close([0, 1, 2], [0], [([0, 1], 2)])
    joint = checked_close([0, 1, 2], [0, 1], [([0, 1], 2)])
    outside = checked_close([0], [1], [])
    if not guarded:
        raise SystemExit("guarded release was refused")
    if not regressing_frontier or regressing_release:
        raise SystemExit("regressing frontier was not refused")
    if alone != [0] or joint != [0, 1, 2] or 2 in (alone or []):
        raise SystemExit("closure disagreed with cross-source compounding")
    if outside is not None:
        raise SystemExit("out-of-universe closure was accepted")
    if reduced_allowed("project-first") or not reduced_allowed("componentwise-sum"):
        raise SystemExit("aggregation gate disagreed with the strict-lift premise")
    return [
        "guarded-release accept",
        "regressing-frontier refuse",
        "out-of-universe refuse",
        "nonstrict-reduction refuse",
        "sum-reduction accept",
    ]


if __name__ == "__main__":
    print("\n".join(classifications()))
