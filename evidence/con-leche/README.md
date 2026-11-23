# con-leche run (local, 2026-11-23)

Command (run in the directory holding both exports):

    con-leche --verified --compare --progress=10% challenge.ndjson solution.ndjson

* con-leche: `leanprover/con-leche` at `bc6676101c488e21ce71a317b33905534d497e14`, built from source with Lean 4.36.0 (`611c117b`), 593 jobs.
* Inputs: `solution.ndjson` sha256 `5ea74b91…f6be244e` (61,570,595,788 bytes), `challenge.ndjson` sha256 `bd484ac9…bdd6ab2b9`.
* Machine: Apple Silicon, 16 cores, 128 GB RAM. Wall clock 03:52:09 → 05:05:18 (+08:00), i.e. 73 min 9 s;
  parse 340.3 s, check 4022.3 s; peak memory footprint 47.4 GB. (Part of the run overlapped with other audit jobs.)
* Exit code 0.

Files: `compare.stdout.log` (verdict), `compare.stderr.log` (progress, statistics and `/usr/bin/time -l` output),
`compare.wallclock.log` (start/end time and exit code).
