import time, json

path = "~/rh-audit/export/solution.ndjson"
t0 = time.time()
CHUNK = 32 * 1024 * 1024

axioms = []
sorry_hits = []
rh_hits = []
lineno = 0
buf = b""
bytes_read = 0
next_report = 10 * 1024**3

with open(path, "rb") as f:
    while True:
        chunk = f.read(CHUNK)
        if not chunk:
            break
        bytes_read += len(chunk)
        data = buf + chunk
        last_nl = data.rfind(b"\n")
        if last_nl == -1:
            buf = data
            continue
        block = data[:last_nl]
        buf = data[last_nl + 1:]

        has_ax = b'"axiom":' in block
        has_sorry = b'"sorryAx"' in block
        has_rh = b'"riemannHypothesis"' in block or b'"rhOfAll"' in block or b'"name":14065054,' in block or b'"name":14065053,' in block

        if has_ax or has_sorry or has_rh:
            cur = lineno
            for line in block.split(b"\n"):
                cur += 1
                if has_ax and b'"axiom":' in line:
                    axioms.append((cur, line.decode("utf-8", errors="replace")))
                    print(f"[{time.time()-t0:.1f}s] AXIOM L{cur}: {line.decode('utf-8', errors='replace')}", flush=True)
                if has_sorry and b'"sorryAx"' in line:
                    sorry_hits.append((cur, line.decode("utf-8", errors="replace")))
                    print(f"[{time.time()-t0:.1f}s] SORRY L{cur}: {line.decode('utf-8', errors='replace')}", flush=True)
                if has_rh and (b'"riemannHypothesis"' in line or b'"rhOfAll"' in line or b'"name":14065054,' in line or b'"name":14065053,' in line):
                    rh_hits.append((cur, line.decode("utf-8", errors="replace")))
            lineno = cur
        else:
            lineno += block.count(b"\n") + 1

        if bytes_read >= next_report:
            print(f"[{time.time()-t0:.1f}s] scanned {bytes_read / 1024**3:.1f} GB (L{lineno:,})", flush=True)
            next_report += 10 * 1024**3

if buf:
    lineno += 1
    if b'"axiom":' in buf:
        axioms.append((lineno, buf.decode("utf-8", errors="replace")))

print(f"\nDONE in {time.time()-t0:.1f}s | total bytes={bytes_read:,} | total lines={lineno:,}")
print(f"TOTAL AXIOM RECORDS: {len(axioms)}")
for ln, txt in axioms:
    print(f"  L{ln}: {txt}")
print(f"TOTAL SORRY HITS: {len(sorry_hits)}")
for ln, txt in sorry_hits:
    print(f"  L{ln}: {txt}")
print(f"RH / rhOfAll HITS ({len(rh_hits)}):")
for ln, txt in rh_hits:
    print(f"  L{ln}: {txt}")
