#!/usr/bin/env python3
"""Split the library build into stages of parallel jobs, for hosted CI runners.

usage: ci_plan.py [--stages S] [--jobs M] [--summary | --stage s --job j]

The library needs about 13 CPU-hours on a fast machine, too close to what one 6-hour job of a 4-core runner can do.
The build is therefore cut into S stages: stages 1..S-1 have M parallel jobs each, and stage S is one job that builds
whatever is left (`lake build`) and runs the checks. Every job of stage s starts from the build outputs of all jobs of
the earlier stages.

The plan is computed from the import graph of the library (read from the sources) and the per-module compile costs in
scripts/ci-costs.tsv (CPU-seconds; modules not listed count 4 s). For each stage, modules are taken in a fixed
topological order and given to the job where they cost least, counting any not-yet-built imports that job would have
to compile as well; a job may therefore repeat a few cheap shared imports of another job. Each job is capped at an
equal share of the remaining work. The computation is deterministic, so every job derives the same plan.

The plan only affects time, never correctness: Lake builds whatever a target needs and is missing.

--stage s --job j prints the targets of that job, one `+Module` per line (nothing for the last stage).
--summary prints the size of each stage.
"""
import argparse, heapq, pathlib, re, sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
LIB = 'ASDExplicitGamma'
CORES = 4
IMPORT = re.compile(r'^\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?(\S+)', re.M)


def graph():
    mods = {}
    for p in sorted((ROOT / LIB).rglob('*.lean')):
        mods['.'.join(p.relative_to(ROOT).with_suffix('').parts)] = p
    root = ROOT / f'{LIB}.lean'
    if root.exists():
        mods[LIB] = root
    imp = {m: sorted(d for d in IMPORT.findall(p.read_text()) if d in mods) for m, p in mods.items()}
    return imp


def costs(imp):
    table = {}
    f = ROOT / 'scripts/ci-costs.tsv'
    if f.exists():
        for line in f.read_text().split('\n'):
            if line and not line.startswith('#'):
                m, c = line.split('\t')
                table[m] = float(c)
    return {m: table.get(m, 4.0) for m in imp}


def plan(stages, jobs):
    imp = graph()
    cost = costs(imp)
    users = {m: [] for m in imp}
    for m, ds in imp.items():
        for d in ds:
            users[d].append(m)
    indeg = {m: len(ds) for m, ds in imp.items()}
    heap = [m for m in imp if indeg[m] == 0]
    heapq.heapify(heap)
    topo = []
    while heap:
        m = heapq.heappop(heap)
        topo.append(m)
        for u in sorted(users[m]):
            indeg[u] -= 1
            if indeg[u] == 0:
                heapq.heappush(heap, u)
    assert len(topo) == len(imp), 'import cycle'
    idx = {m: i for i, m in enumerate(topo)}
    c = [cost[m] for m in topo]
    deps = [[idx[d] for d in imp[m]] for m in topo]
    clo = []
    for i in range(len(topo)):
        b = 1 << i
        for d in deps[i]:
            b |= clo[d]
        clo.append(b)

    def bits(x):
        while x:
            low = x & -x
            yield low.bit_length() - 1
            x ^= low

    total = sum(c)
    built = 0
    out = []
    for s in range(stages - 1):
        remaining = total - sum(c[k] for k in bits(built))
        cap = remaining / (jobs * CORES) / (stages - 1 - s) * 1.1
        job = [0] * jobs
        load = [0.0] * jobs
        for i in range(len(topo)):
            if (built >> i) & 1 or any((job[j] >> i) & 1 for j in range(jobs)):
                continue
            best = None
            unbuilt = clo[i] & ~built
            whole = None  # cost of all of `unbuilt`, computed at most once
            for j in range(jobs):
                miss = unbuilt & ~job[j]
                if miss == 1 << i:
                    extra = c[i] / CORES
                elif miss == unbuilt:
                    if whole is None:
                        whole = sum(c[k] for k in bits(unbuilt)) / CORES
                    extra = whole
                else:
                    extra = sum(c[k] for k in bits(miss)) / CORES
                if load[j] + extra <= cap and (best is None or (extra, load[j], j) < best):
                    best = (extra, load[j], j)
            if best is None:
                continue
            extra, _, j = best
            job[j] |= clo[i] & ~built
            load[j] += extra
        stage = []
        for j in range(jobs):
            members = [topo[k] for k in bits(job[j])]
            inside = set(members)
            sinks = sorted(m for m in members if not any(u in inside for u in users[m]))
            stage.append({'modules': len(members), 'hours': load[j] * CORES / 3600, 'targets': sinks})
        out.append(stage)
        for j in range(jobs):
            built |= job[j]
    rest = [m for m in topo if not (built >> idx[m]) & 1]
    return out, rest, cost


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--stages', type=int, default=4)
    ap.add_argument('--jobs', type=int, default=8)
    ap.add_argument('--stage', type=int)
    ap.add_argument('--job', type=int)
    ap.add_argument('--summary', action='store_true')
    a = ap.parse_args()
    out, rest, cost = plan(a.stages, a.jobs)
    if a.summary:
        for s, stage in enumerate(out, 1):
            print(f'stage {s}: ' + ', '.join(f'{j["modules"]} mods/{j["hours"]:.2f} CPU-h' for j in stage))
        print(f'stage {a.stages} (final): {len(rest)} mods/{sum(cost[m] for m in rest) / 3600:.2f} CPU-h')
        return
    if a.stage is None or a.job is None:
        sys.exit(__doc__)
    if a.stage < a.stages:
        for t in out[a.stage - 1][a.job]['targets']:
            print('+' + t)


if __name__ == '__main__':
    main()
