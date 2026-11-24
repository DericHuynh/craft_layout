"""Check whether arrivals can join the old packed ranks or the old total order."""

from argparse import ArgumentParser
from collections import defaultdict
from heapq import heapify, heappop, heappush
from pathlib import Path


def read_trace(path):
    frame = None
    with path.open() as stream:
        for line in stream:
            match line.split():
                case ["frame", _]:
                    if frame is not None:
                        yield frame
                    frame = set(), set(), {}
                case ["v", vertex]:
                    frame[0].add(int(vertex))
                case ["e", producer, reader]:
                    frame[1].add((int(producer), int(reader)))
                case ["#", "rank", vertex, rank]:
                    frame[2][int(vertex)] = int(rank)
                case [str(comment), *_] if comment.startswith("#"):
                    continue
                case []:
                    continue
                case _:
                    raise ValueError(f"invalid trace row in {path}: {line}")
    if frame is not None:
        yield frame


def topological_order(vertices, edges):
    predecessors = dict.fromkeys(vertices, 0)
    outgoing = defaultdict(list)
    for producer, reader in edges:
        outgoing[producer].append(reader)
        predecessors[reader] += 1
    ready = [vertex for vertex in vertices if predecessors[vertex] == 0]
    heapify(ready)
    result = []
    while ready:
        producer = heappop(ready)
        result.append(producer)
        for reader in outgoing[producer]:
            predecessors[reader] -= 1
            if predecessors[reader] == 0:
                heappush(ready, reader)
    if len(result) != len(vertices):
        raise ValueError("the rank admission check requires an acyclic trace")
    return result


def admissions(active, edges, pinned, ordered, *, gaps):
    # Odd coordinates are gaps between frozen positions and may hold multiple
    # arrivals, tied by their topological order.
    incoming = defaultdict(list)
    for producer, reader in edges:
        incoming[reader].append(producer)
    assigned = dict(pinned)
    for reader in ordered:
        if reader in pinned:
            continue
        if gaps:
            assigned[reader] = max(
                (assigned[producer] + (producer in pinned) for producer in incoming[reader]),
                default=-1,
            )
        else:
            assigned[reader] = max(
                (assigned[producer] + 1 for producer in incoming[reader]),
                default=0,
            )
    if gaps:
        return all(assigned[a] < assigned[b] for a, b in edges if b in pinned)
    return all(assigned[a] < assigned[b] for a, b in edges) and all(
        assigned[v] < 0xFFFF for v in active
    )


FIELDS = (
    "new_ids", "returning_ids", "retained_engine_rank_changes",
    "changed_historical_rank_on_return", "backward_cached_rank_frames",
    "cannot_pin_previous_integer_ranks_frames", "cannot_pin_previous_total_order_frames",
)


def evaluate(path):
    previous = {}
    seen = {}
    stats = dict.fromkeys(FIELDS, 0)
    for index, (active, edges, ranks) in enumerate(read_trace(path)):
        if set(ranks) != active:
            raise ValueError(f"{path} lacks complete rank rows, set LAYOUT_TRACE_RANKS=1")
        if index:
            retained = active & previous.keys()
            arriving = active - previous.keys()
            returning = arriving & seen.keys()
            stats["new_ids"] += len(arriving - seen.keys())
            stats["returning_ids"] += len(returning)
            stats["retained_engine_rank_changes"] += sum(previous[v] != ranks[v] for v in retained)
            stats["changed_historical_rank_on_return"] += sum(seen[v] != ranks[v] for v in returning)
            cached = {v: seen.get(v, rank) for v, rank in ranks.items()}
            stats["backward_cached_rank_frames"] += any(cached[a] >= cached[b] for a, b in edges)
            ordered = topological_order(active, edges)
            retained_ranks = {v: previous[v] for v in retained}
            stats["cannot_pin_previous_integer_ranks_frames"] += not admissions(
                active, edges, retained_ranks, ordered, gaps=False,
            )
            by_rank = sorted(retained, key=lambda v: (previous[v], v))
            retained_order = {v: 2 * j for j, v in enumerate(by_rank)}
            stats["cannot_pin_previous_total_order_frames"] += not admissions(
                active, edges, retained_order, ordered, gaps=True,
            )
        previous = ranks
        seen.update(ranks)
    return stats


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("trace_directory", type=Path)
    args = parser.parse_args()
    print("fixture", *FIELDS, sep="\t")
    for path in sorted(args.trace_directory.glob("*.tsv")):
        stats = evaluate(path)
        print(path.stem, *(stats[field] for field in FIELDS), sep="\t")


if __name__ == "__main__":
    main()
