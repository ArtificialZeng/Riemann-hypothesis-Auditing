import json, time

path = "~/rh-audit/export/solution.ndjson"
t0 = time.time()

names = {0: ""}
target_ies = {6490658, 6497236}
found_ies = {}
RH_nids = {}
RH_decls = []
decl_341189 = None
name_341189_line = None
axioms_early = []

lineno = 0
buf = b""
CHUNK = 16 * 1024 * 1024

with open(path, "rb") as f:
    bytes_read = 0
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

        for line in block.split(b"\n"):
            lineno += 1
            if b'"in":' in line:
                obj = json.loads(line)
                if "in" in obj:
                    nid = obj["in"]
                    if "str" in obj:
                        p = obj["str"]["pre"]
                        s = obj["str"]["str"]
                        pre = names.get(p, f"<{p}>")
                        full = f"{pre}.{s}" if pre else s
                        names[nid] = full
                        if s == "RiemannHypothesis":
                            RH_nids[nid] = (lineno, full, line.decode().strip())
                            print(f"[{time.time()-t0:.1f}s] RH NAME L{lineno}: {line.decode().strip()} ({full})", flush=True)
                        if nid == 341189:
                            name_341189_line = (lineno, full, line.decode().strip())
                            print(f"[{time.time()-t0:.1f}s] 341189 NAME L{lineno}: {line.decode().strip()} ({full})", flush=True)
                    elif "num" in obj:
                        p = obj["num"]["pre"]
                        i = obj["num"]["i"]
                        pre = names.get(p, f"<{p}>")
                        names[nid] = f"{pre}.{i}" if pre else str(i)
            elif b'"axiom":' in line:
                obj = json.loads(line)
                if "axiom" in obj:
                    ax = obj["axiom"]
                    axioms_early.append((lineno, ax["name"], names.get(ax["name"]), ax["type"], line.decode().strip()))
            elif b'6490658' in line or b'6497236' in line:
                if b'"ie":' in line:
                    obj = json.loads(line)
                    ie = obj.get("ie")
                    if ie in target_ies:
                        found_ies[ie] = (lineno, line.decode().strip(), obj)
                        print(f"[{time.time()-t0:.1f}s] FOUND ie={ie} L{lineno}: {line.decode().strip()}", flush=True)
            elif b'"name":341189,' in line or b'"name":341189}' in line:
                if b'"thm":' in line or b'"def":' in line or b'"axiom":' in line:
                    decl_341189 = (lineno, line.decode().strip())
                    print(f"[{time.time()-t0:.1f}s] FOUND 341189 DECL L{lineno}: {line.decode().strip()}", flush=True)
            elif RH_nids and (b'"def":' in line or b'"thm":' in line or b'"axiom":' in line):
                for nid in RH_nids:
                    if f'"name":{nid},'.encode() in line or f'"name":{nid}}}'.encode() in line:
                        RH_decls.append((lineno, nid, line.decode().strip()))
                        print(f"[{time.time()-t0:.1f}s] FOUND RH DECL L{lineno}: {line.decode().strip()}", flush=True)

        if len(found_ies) == len(target_ies) and decl_341189 and RH_decls:
            print(f"[{time.time()-t0:.1f}s] ALL TARGETS FOUND at byte {bytes_read:,} (L{lineno:,})", flush=True)
            break

print("\n=== SUMMARY ===")
for ie, (ln, raw, obj) in sorted(found_ies.items()):
    extra = ""
    if "const" in obj:
        cid = obj["const"]["name"]
        extra = f" ==> const {names.get(cid)} (nid={cid}, us={obj['const']['us']})"
    print(f"ie={ie} (L{ln}): {raw}{extra}")

print("RH_nids:", RH_nids)
print("RH_decls:", RH_decls)
print("name_341189:", name_341189_line)
print("decl_341189:", decl_341189)
print(f"Early axioms up to L{lineno} ({len(axioms_early)}):")
for a in axioms_early:
    print(" ", a)
