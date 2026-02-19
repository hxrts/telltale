# V2 Baseline Artifacts

This directory is the frozen WS0 baseline snapshot for V2.

- `suite_manifest.json`: canonical benchmark + conformance corpus definition.
- `metrics.json`: baseline throughput/latency/lock-contention capture plus `EnvelopeDiff` artifact.
- `conformance.json`: baseline canonical/threaded conformance pass rates.
- `hash_snapshot.json`: SHA-256 snapshot over the three baseline artifacts above.

## Regeneration

Run:

```bash
just v2-freeze-baseline
```

## CI Validation

Run:

```bash
just check-v2-baseline
```

The check validates artifact presence, hash consistency, and required schema fields.
